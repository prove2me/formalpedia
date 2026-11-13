-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB171_original_dividend_locally_bounded_variation
-- name    : AvramDividend.Classical.avram_gbB171_original_dividend_locally_bounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:32:24.430188+00:00
-- url     : https://prove2.me/theorems/7e8345f8-cd60-4eb9-952f-577baf6e5dd0
-- title:
--   Original dividend strategy has locally bounded variation on each sample path
-- statement:
--   An admissible dividend strategy has monotone real sample paths, hence locally bounded total variation on every finite nonnegative-time interval. This is the finite-variation ingredient in the semimartingale local-time occupation route to original Gaussian B169/B141.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB171_original_dividend_locally_bounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    LocallyBoundedVariationOn (fun t : ℝ≥0 => D t ω) Set.univ := by sorry
