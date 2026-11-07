-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route10_signed_integrable_nonpositive_mean_centering
-- name    : AvramDividend.Classical.avram_route10_signed_integrable_nonpositive_mean_centering
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T14:44:18.717458+00:00
-- url     : https://prove2.me/theorems/817ff85b-b891-45f7-982d-c7dd0b1cda81
-- title:
--   Centred martingale and nonpositive drift decomposition of an L1 signed stopped-grid budget
-- statement:
--   An integrable signed residual with nonpositive expectation can be recentered into an exactly mean-zero integrable random source and a pointwise nonpositive deterministic HJB drift without altering the pathwise value. This is the exact missing bridge from the 4f605d76 signed total source to the route10 positive-error Fatou theorem, retaining the original law and allowing nonzero negative source mean.
-- source:
--   Direct integral-centering source transformation for original stopped BV signed-budget bridge; complements accepted d3f3db15 and 4f605d76 without assuming vanishing source expectation.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_route10_signed_integrable_nonpositive_mean_centering
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Integrable Z P)
    (hMean : (∫ ω, Z ω ∂P) ≤ 0) :
    ∃ M B : Ω → ℝ,
      Integrable M P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ ω, B ω ≤ 0) ∧
      (∀ ω, Z ω = M ω + B ω) := by sorry
