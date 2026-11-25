module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
import Mathlib.MeasureTheory.Integral.ExpDecay

/-! # Laplace transforms of the translations along a norm section on the strip space

Masullo, §10.4.2, pp. 459–464; this file belongs to the open statement
`Isolated.spectralStripConvolution_hilbertSchmidt_of_le_one` (#7405) and nothing imports it.

Let `τ` be a continuous section of the idele class norm and `W` the weighted space of the strip
of half-width `α` at order `s`. The translations `x ↦ T (τ (exp x))` of `W` grow at most like
`exp (α |x|) (1 + |x|) ^ (s / 2)`, so for a rate `L > α` their one-sided Laplace transforms

`P⁺ u = ∫ x in Ioi 0, exp (-L x) • T (τ (exp x)) u`, `P⁻ u = ∫ x in Ioi 0, exp (-L x) • T (τ (exp (-x))) u`

are bounded operators of `W`. Their sum is convolution along the section with `exp (-L |x|)`, the
operator `R` of step 2 of the argument on #7405. Neither is the action of a compactly supported
test.

* `norm_hardySobolevTranslation_section_le`, `continuous_hardySobolevTranslation_section`: the
  growth bound and the strong continuity of the translations along the section.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
variable {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "T(" g ")" => hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs g
local notation "expU(" x ")" =>
  (Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne' : ℝ≥0ˣ)

section Section

/-- The exponential is continuous into the positive real units. -/
private theorem continuous_expUnits : Continuous fun x : ℝ ↦ expU(x) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_real_toNNReal.comp Real.continuous_exp
  · have h : (fun x : ℝ ↦ ((expU(x)⁻¹ : ℝ≥0ˣ) : ℝ≥0)) = fun x : ℝ ↦ (Real.exp (-x)).toNNReal := by
      funext x
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, Real.exp_neg, Real.toNNReal_inv]
    rw [h]
    exact continuous_real_toNNReal.comp (Real.continuous_exp.comp continuous_neg)

/-- The exponential into the positive real units is additive-to-multiplicative. -/
private theorem expUnits_add (x y : ℝ) : expU(x + y) = expU(x) * expU(y) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, Real.exp_add,
    Real.toNNReal_mul (Real.exp_pos x).le]

/-- The exponential into the positive real units sends zero to one. -/
private theorem expUnits_zero : expU((0 : ℝ)) = 1 := by
  apply Units.ext
  rw [Units.val_mk0, Real.exp_zero, Real.toNNReal_one, Units.val_one]

/-- The logarithm of the norm along a norm section is the logarithmic coordinate. -/
private theorem logIdeleClassNorm_section (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (x : ℝ) :
    logIdeleClassNorm F (τ expU(x)) = x := by
  change Real.log ((ideleClassNorm F (τ expU(x))).val : ℝ) = x
  rw [hτ expU(x), Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]

/-- Paper: Lemma 9.3.1.5, p. 421, along a section of the idele class norm. The translation of
the strip space by the point of the section at logarithmic coordinate `x` has operator norm at
most `exp (α |x|) (1 + |x|) ^ (s / 2)`.
Deviation: The paper does not single out a section; this is the bound of the lemma in the
coordinate of the section. -/
theorem norm_hardySobolevTranslation_section_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (x : ℝ) :
    ‖T(τ expU(x))‖ ≤ Real.exp (α * |x|) * (1 + |x|) ^ (s / 2) := by
  have h := norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-α) α s hI hs (τ expU(x))
  have hlog : Real.log ((m𝔽 (τ expU(x))).val : ℝ) = x := logIdeleClassNorm_section τ hτ x
  beta_reduce at h
  rw [hlog] at h
  refine h.trans_eq ?_
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos hx, max_eq_left]
    · congr 1
      ring
    · exact Real.exp_le_exp.mpr (by nlinarith)

/-- Paper: Lemma 9.3.1.5, p. 421, along a section of the idele class norm. The translate of a
vector of the strip space by the point of the section at logarithmic coordinate `x` has norm at
most `exp (α |x|) (1 + |x|) ^ (s / 2)` times the norm of the vector. -/
theorem norm_hardySobolevTranslation_section_apply_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (x : ℝ) (u : W) :
    ‖T(τ expU(x)) u‖ ≤ Real.exp (α * |x|) * (1 + |x|) ^ (s / 2) * ‖u‖ :=
  ((T(τ expU(x))).le_opNorm u).trans (mul_le_mul_of_nonneg_right
    (norm_hardySobolevTranslation_section_le hα hs τ hτ x) (norm_nonneg u))

/-- Paper: Definition 9.3.1.1, p. 419, along a section of the idele class norm. The translates
of a vector of the strip space along the section depend continuously on the logarithmic
coordinate. -/
theorem continuous_hardySobolevTranslation_section (τ : ℝ≥0ˣ →ₜ* C𝔽) (u : W) :
    Continuous fun x : ℝ ↦ T(τ expU(x)) u :=
  (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs).choose_spec.2.comp
    ((τ.continuous.comp continuous_expUnits).prodMk continuous_const)

end Section

section Abstract

/-- A real power of `1 + x` times a decaying exponential is integrable on the positive
half-line. -/
private theorem integrableOn_exp_neg_mul_one_add_rpow {c : ℝ} (hc : 0 < c) (p : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-c * x) * (1 + x) ^ p) (Ioi 0) := by
  have hc2 : 0 < c / 2 := by positivity
  refine integrable_of_isBigO_exp_neg hc2 ?_ ?_
  · refine ContinuousOn.mul (by fun_prop)
      (ContinuousOn.rpow_const (by fun_prop) fun x hx ↦ Or.inl ?_)
    have h0 : (0 : ℝ) ≤ x := hx
    positivity
  · have h0 : Tendsto
        (fun x : ℝ ↦ Real.exp (c / 2) * ((1 + x) ^ p * Real.exp (-(c / 2) * (1 + x))))
        atTop (𝓝 (Real.exp (c / 2) * 0)) :=
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (c / 2) hc2).comp
        (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)).const_mul _
    have h1 : (fun x : ℝ ↦ Real.exp (-c * x) * (1 + x) ^ p) = fun x ↦
        (Real.exp (c / 2) * ((1 + x) ^ p * Real.exp (-(c / 2) * (1 + x)))) *
          Real.exp (-(c / 2) * x) := by
      funext x
      have h : Real.exp (-c * x) =
          Real.exp (c / 2) * Real.exp (-(c / 2) * (1 + x)) * Real.exp (-(c / 2) * x) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [h]
      ring
    rw [h1]
    simpa using (h0.isBigO_one ℝ).mul
      (Asymptotics.isBigO_refl (fun x : ℝ ↦ Real.exp (-(c / 2) * x)) atTop)

/-- The one-sided Laplace transform of a strongly continuous family of operators of a Banach
space that grows at most like `exp (a x) (1 + x) ^ p` is, at every rate `L > a`, a bounded
operator, with the integral of the majorant as a bound for its norm. -/
private theorem exists_laplace_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (U : ℝ → E →L[ℂ] E) (hcont : ∀ w, Continuous fun x ↦ U x w)
    {a p L : ℝ} (hL : a < L) (hU : ∀ x, 0 ≤ x → ‖U x‖ ≤ Real.exp (a * x) * (1 + x) ^ p) :
    ∃ P : E →L[ℂ] E,
      (∀ w, IntegrableOn (fun x ↦ Real.exp (-L * x) • U x w) (Ioi 0) ∧
        P w = ∫ x in Ioi 0, Real.exp (-L * x) • U x w) ∧
      ‖P‖ ≤ ∫ x in Ioi 0, Real.exp (-(L - a) * x) * (1 + x) ^ p := by
  have hmaj := integrableOn_exp_neg_mul_one_add_rpow (sub_pos.mpr hL) p
  have hbound (w : E) (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      ‖Real.exp (-L * x) • U x w‖ ≤ Real.exp (-(L - a) * x) * (1 + x) ^ p * ‖w‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-L * x) * ‖U x w‖
        ≤ Real.exp (-L * x) * (Real.exp (a * x) * (1 + x) ^ p * ‖w‖) :=
          mul_le_mul_of_nonneg_left (((U x).le_opNorm w).trans
            (mul_le_mul_of_nonneg_right (hU x (le_of_lt hx)) (norm_nonneg w))) (Real.exp_pos _).le
      _ = Real.exp (-(L - a) * x) * (1 + x) ^ p * ‖w‖ := by
          rw [← mul_assoc, ← mul_assoc, ← Real.exp_add]
          congr 3
          ring
  have hint (w : E) : IntegrableOn (fun x ↦ Real.exp (-L * x) • U x w) (Ioi 0) :=
    Integrable.mono' (hmaj.mul_const ‖w‖)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
        (hcont w)).aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ hbound w x hx)
  let P₀ : E →ₗ[ℂ] E :=
    { toFun := fun w ↦ ∫ x in Ioi 0, Real.exp (-L * x) • U x w
      map_add' := fun v w ↦ by
        simp only [map_add, smul_add]
        exact integral_add (hint v) (hint w)
      map_smul' := fun c w ↦ by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (.of_forall fun x ↦ smul_comm _ _ _) }
  refine ⟨P₀.mkContinuous (∫ x in Ioi 0, Real.exp (-(L - a) * x) * (1 + x) ^ p) fun w ↦ ?_,
    fun w ↦ ⟨hint w, rfl⟩, LinearMap.mkContinuous_norm_le _ ?_ _⟩
  · calc ‖∫ x in Ioi 0, Real.exp (-L * x) • U x w‖
        ≤ ∫ x in Ioi 0, Real.exp (-(L - a) * x) * (1 + x) ^ p * ‖w‖ :=
          norm_integral_le_of_norm_le (hmaj.mul_const ‖w‖)
            ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ hbound w x hx)
      _ = (∫ x in Ioi 0, Real.exp (-(L - a) * x) * (1 + x) ^ p) * ‖w‖ := integral_mul_const _ _
  · exact setIntegral_nonneg measurableSet_Ioi fun x hx ↦
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _)

/-- A continuous functional that is multiplied by `exp (z x)` along a family of vectors takes
the value `(L - z)⁻¹` times the constant on its Laplace transform at a rate `L > re z`. -/
private theorem laplace_apply_of_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (Λ : E →L[ℂ] ℂ) (f : ℝ → E) {L : ℝ} {z c : ℂ} (hz : z.re < L)
    (hf : IntegrableOn (fun x ↦ Real.exp (-L * x) • f x) (Ioi 0))
    (hΛ : ∀ x : ℝ, Λ (f x) = Complex.exp (z * x) * c) :
    Λ (∫ x in Ioi 0, Real.exp (-L * x) • f x) = ((L : ℂ) - z)⁻¹ * c := by
  rw [← Λ.integral_comp_comm hf]
  have h (x : ℝ) : Λ (Real.exp (-L * x) • f x) = Complex.exp ((z - L) * x) * c := by
    rw [Λ.map_smul_of_tower, hΛ, Complex.real_smul, Complex.ofReal_exp, ← mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [h]
  have hre : (z - (L : ℂ)).re < 0 := by simpa using hz
  rw [integral_mul_const, integral_exp_mul_complex_Ioi hre 0, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, neg_div, ← div_neg, neg_sub, one_div]

/-- On a group with a left-invariant measure, the product integral of a left translate with a
second function moves the translation to the second function. -/
private theorem integral_translate_mul {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (h : G) (a b f J : G → ℂ)
    (ha : a =ᵐ[μ] fun x ↦ f (h⁻¹ * x)) (hb : b =ᵐ[μ] J) :
    ∫ x, a x * b x ∂μ = ∫ y, f y * J (h * y) ∂μ := by
  have h1 : (fun x ↦ a x * b x) =ᵐ[μ] fun x ↦ f (h⁻¹ * x) * J x := by
    filter_upwards [ha, hb] with x hx hy
    rw [hx, hy]
  rw [integral_congr_ae h1, ← integral_mul_left_eq_self (μ := μ) (fun x ↦ f (h⁻¹ * x) * J x) h]
  simp only [inv_mul_cancel_left]

end Abstract

section Laplace

/-- For a rate `L` above the half-width of the strip, the Laplace transform of the translations
along a norm section in the direction of increasing norm is a bounded operator of the strip
space. The integral of each orbit converges, and the operator norm is at most the integral of
`exp (-(L - α) x) (1 + x) ^ (s / 2)` over the positive half-line. -/
theorem exists_spectralStripForwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) :
    ∃ P : W →L[ℂ] W,
      (∀ u, IntegrableOn (fun x ↦ Real.exp (-L * x) • T(τ expU(x)) u) (Ioi 0) ∧
        P u = ∫ x in Ioi 0, Real.exp (-L * x) • T(τ expU(x)) u) ∧
      ‖P‖ ≤ ∫ x in Ioi 0, Real.exp (-(L - α) * x) * (1 + x) ^ (s / 2) :=
  exists_laplace_clm (fun x ↦ T(τ expU(x)))
    (continuous_hardySobolevTranslation_section hα hs τ) hL fun x hx ↦ by
      simpa only [abs_of_nonneg hx] using norm_hardySobolevTranslation_section_le hα hs τ hτ x

/-- For a rate `L` above the half-width of the strip, the Laplace transform of the translations
along a norm section in the direction of decreasing norm is a bounded operator of the strip
space, with the same bound as the forward transform. -/
theorem exists_spectralStripBackwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) :
    ∃ P : W →L[ℂ] W,
      (∀ u, IntegrableOn (fun x ↦ Real.exp (-L * x) • T(τ expU(-x)) u) (Ioi 0) ∧
        P u = ∫ x in Ioi 0, Real.exp (-L * x) • T(τ expU(-x)) u) ∧
      ‖P‖ ≤ ∫ x in Ioi 0, Real.exp (-(L - α) * x) * (1 + x) ^ (s / 2) :=
  exists_laplace_clm (fun x ↦ T(τ expU(-x)))
    (fun u ↦ (continuous_hardySobolevTranslation_section hα hs τ u).comp continuous_neg) hL
    fun x hx ↦ by
      simpa only [abs_neg, abs_of_nonneg hx] using
        norm_hardySobolevTranslation_section_le hα hs τ hτ (-x)

/-- Reconstruction: the forward half of the operator `R` of step 2 of the argument for
Theorem 10.4.2.1 posted on #7405; it is not in the paper. It is the Laplace transform at the
rate `L` of the translations of the strip space along a section of the idele class norm, in the
direction of increasing norm: `u ↦ ∫ x in Ioi 0, exp (-L x) • T (τ (exp x)) u`. The sum with
`spectralStripBackwardLaplace` is convolution along the section with `exp (-L |x|)`. -/
def spectralStripForwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) : W →L[ℂ] W :=
  (exists_spectralStripForwardLaplace hα hs τ hτ hL).choose

/-- Reconstruction: the backward half of the operator `R` of step 2 of the argument for
Theorem 10.4.2.1 posted on #7405; it is not in the paper. It is the Laplace transform at the
rate `L` of the translations of the strip space along a section of the idele class norm, in the
direction of decreasing norm: `u ↦ ∫ x in Ioi 0, exp (-L x) • T (τ (exp (-x))) u`. -/
def spectralStripBackwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) : W →L[ℂ] W :=
  (exists_spectralStripBackwardLaplace hα hs τ hτ hL).choose

/-- The forward Laplace transform is the integral of the damped forward orbit. -/
theorem spectralStripForwardLaplace_apply (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) (u : W) :
    spectralStripForwardLaplace hα hs τ hτ hL u =
      ∫ x in Ioi 0, Real.exp (-L * x) • T(τ expU(x)) u :=
  ((exists_spectralStripForwardLaplace hα hs τ hτ hL).choose_spec.1 u).2

/-- The damped forward orbit of a vector of the strip space is integrable. -/
theorem integrableOn_spectralStripForwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) (u : W) :
    IntegrableOn (fun x ↦ Real.exp (-L * x) • T(τ expU(x)) u) (Ioi 0) :=
  ((exists_spectralStripForwardLaplace hα hs τ hτ hL).choose_spec.1 u).1

/-- The forward Laplace transform has operator norm at most the integral of
`exp (-(L - α) x) (1 + x) ^ (s / 2)` over the positive half-line. -/
theorem norm_spectralStripForwardLaplace_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) :
    ‖spectralStripForwardLaplace hα hs τ hτ hL‖ ≤
      ∫ x in Ioi 0, Real.exp (-(L - α) * x) * (1 + x) ^ (s / 2) :=
  (exists_spectralStripForwardLaplace hα hs τ hτ hL).choose_spec.2

/-- The backward Laplace transform is the integral of the damped backward orbit. -/
theorem spectralStripBackwardLaplace_apply (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) (u : W) :
    spectralStripBackwardLaplace hα hs τ hτ hL u =
      ∫ x in Ioi 0, Real.exp (-L * x) • T(τ expU(-x)) u :=
  ((exists_spectralStripBackwardLaplace hα hs τ hτ hL).choose_spec.1 u).2

/-- The damped backward orbit of a vector of the strip space is integrable. -/
theorem integrableOn_spectralStripBackwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) (u : W) :
    IntegrableOn (fun x ↦ Real.exp (-L * x) • T(τ expU(-x)) u) (Ioi 0) :=
  ((exists_spectralStripBackwardLaplace hα hs τ hτ hL).choose_spec.1 u).1

/-- The backward Laplace transform has operator norm at most the integral of
`exp (-(L - α) x) (1 + x) ^ (s / 2)` over the positive half-line. -/
theorem norm_spectralStripBackwardLaplace_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) :
    ‖spectralStripBackwardLaplace hα hs τ hτ hL‖ ≤
      ∫ x in Ioi 0, Real.exp (-(L - α) * x) * (1 + x) ^ (s / 2) :=
  (exists_spectralStripBackwardLaplace hα hs τ hτ hL).choose_spec.2

end Laplace

end RiemannMasullo.Isolated
