-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_capped_dividendMeasure_atom_bound
-- name    : AvramDividend.Classical.local_verification_capped_dividendMeasure_atom_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:26:19.790918+00:00
-- url     : https://prove2.me/theorems/520e9f75-8da8-42d6-982a-f68012e70665
-- title:
--   Actual discounted Stieltjes atom paid under Proposition 4 HJB hypotheses is bounded by the general verification value drop
-- statement:
--   For every capped admissible strategy, every active or time-zero right dividend jump, and the exact generic BV/UBV HJB assumptions from local_verification, the discounted Stieltjes measure's mass at that time is bounded by the discounted decrease of w across the dividend. This combines the rigorous atomic dividendMeasure identity, the full-cap HJB jump estimate including boundaries, and the positivity of exponential discounting. It directly addresses the singular atomic dividend-payment component of the original theorem.
-- source:
--   Children dividendMeasure_singleton_eq_rightLimit_sub and local_verification_capped_admissible_jump_bound; pinned Mathlib ENNReal.ofReal_mul and ofReal_le_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_capped_dividendMeasure_atom_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      dividendMeasure D ω {(t : ℝ)} ≤
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
      (w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))) := by sorry
