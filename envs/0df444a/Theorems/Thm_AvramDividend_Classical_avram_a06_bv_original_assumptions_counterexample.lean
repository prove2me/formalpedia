-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_bv_original_assumptions_counterexample
-- name    : AvramDividend.Classical.avram_a06_bv_original_assumptions_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T15:08:39.808684+00:00
-- url     : https://prove2.me/theorems/696ceb2d-4bea-48f7-b965-dbba0057128c
-- title:
--   A06 BV original hypotheses hold at zero cap despite a finite-horizon cash violation
-- statement:
--   For any Standing bounded-variation finite-activity spectrally negative Levy process, the full original A06 hypotheses admit C=0, x=0, w=0 and an admissible zero-barrier dividend strategy, but the claimed expected discounted dividend inequality fails at a finite horizon. This theorem is conditional on a qualifying source and exposes the exact missing positive-cap premise.
-- source:
--   Root-connected conditional counterexample derived from the authoritative Proved admissible barrier theorem 3289af7b. The generator and derivative requirements are vacuous on the empty interior at zero cap; the no-right-jump proof supplies the dividend jump control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_zero_cap_conditional_refutation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_bv_original_assumptions_counterexample
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ (w : ℝ → ℝ) (C : ℝ≥0∞) (x : ℝ)
      (D : ℝ≥0 → Ω → ℝ) (T : ℝ),
      ContinuousOn w (Ici 0) ∧
      (∀ y < 0, w y = 0) ∧
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
      ENNReal.ofReal x ≤ C ∧
      IsAdmissibleLe X x C D ∧
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) ∧
      (∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) ∧
      0 ≤ T ∧
      ¬ ((∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) := by sorry
