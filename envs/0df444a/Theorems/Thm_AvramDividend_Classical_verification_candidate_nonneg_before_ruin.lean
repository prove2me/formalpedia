-- Prove2me | Theorems.Thm_AvramDividend_Classical_verification_candidate_nonneg_before_ruin
-- name    : AvramDividend.Classical.verification_candidate_nonneg_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T11:23:10.469006+00:00
-- url     : https://prove2.me/theorems/5beeeabf-651d-4e4a-b23f-0bec5ac2a8a1
-- title:
--   Verification candidate is nonnegative on capped controlled reserves before ruin
-- statement:
--   For a capped admissible dividend policy, at every strictly positive time before ruin the controlled reserve is between zero and the cap. The HJB supersolution therefore dominates that reserve and is nonnegative. This is the terminal-value nonnegativity used when discarding the stopped w(U) term in the verification inequality.
-- source:
--   Combination of the capped-policy definition, the ruin-time pathwise lower bound, and the proved HJB capital lower bound; supports Proposition 4(i) of Avram–Palmowski–Pistorius.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_hjb_candidate_ge_capital
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.verification_candidate_nonneg_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht0 : 0 < t)
    (htru : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ w (riskProcess X x D t ω) := by sorry
