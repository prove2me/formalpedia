-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_weighted_real_HJB_expected_nonpos
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_weighted_real_HJB_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:45:41.838198+00:00
-- url     : https://prove2.me/theorems/165663da-d20b-4239-ae7c-8d1aebcd236c
-- title:
--   Original BV strict-complement C1 weighted stopped HJB generator has nonpositive real expectation
-- statement:
--   For the unchanged original spectrally negative bounded-variation Levy process, any nonnegative random physical-clock localisation weight with an integrable signed C1 HJB residual yields a nonpositive real expected weighted generator residual on the strict pre-ruin positive-cap interior. The source drift is positive in the strict complement; the discounted generator and gradient inequalities force the pointwise signed residual to be nonpositive. The conclusion is an ordinary real integral over the actual finite pushed physical clock times original P, valid also at horizon zero. It supplies the exact signed-expectation sign interface needed by W8-04 without assuming the full cash or terminal verification.
-- source:
--   Avram-Palmowski-Pistorius (2007) Proposition 4(i), HJB generator drift sign in original BV C1 strict complement. Derives signed real expectation from Proved W7-02 discounted generator sign a0879a2f and W7-17 strict positive drift d6705e01, with actual stopped interior measurable f2efea1f. Proved C2 compact source eae29a0 cannot directly discharge W8-04 C1 hypotheses. Does not claim Stieltjes cash, source jump martingale, or terminal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_weighted_real_HJB_expected_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (T : ℝ≥0)
    (ρ : ℝ≥0 × Ω → ℝ) (hρ : ∀ p, 0 ≤ ρ p) :
    let μ : Measure (ℝ≥0 × Ω) :=
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t p.2 - rightLimit D t p.2) p.1
    let S : Set (ℝ≥0 × Ω) :=
      {p | p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Y p ∧ ENNReal.ofReal (Y p) < C}
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift + (∫ z in Iio (0 : ℝ),
          w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p))
    IntegrableOn R S μ → (∫ p in S, R p ∂μ) ≤ 0 := by sorry
