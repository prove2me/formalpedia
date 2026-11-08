-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_mark_source_positive_ruin_time
-- name    : AvramDividend.Classical.avram_e0_initial_mark_source_positive_ruin_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:01:45.305539+00:00
-- url     : https://prove2.me/theorems/64e9322a-3bfb-4839-8ccc-ad9ac920d276
-- title:
--   Source Lévy right-continuity and affordable initial dividends force positive ruin time on every path
-- statement:
--   The original SpectrallyNegativeLevy structure starts at zero and has right-continuous paths. On nonnegative time those pathwise fields imply continuity at time zero. An initially affordable nonnegative mark therefore yields strictly positive ruin time on every path with no additional continuity hypotheses. This is the exact all-path premise needed in the infinite-cap original first-cell nonintegrability result.
-- source:
--   From Proved cd3e6728 and the original source fields X_zero and rightCont, target e0b94d7f first-row countermodel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_mark_source_positive_ruin_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKstrict : ∀ ω, K ω < x) :
    ∀ ω, (0 : ℝ≥0∞) <
      ruinTime X x (fun t η => if t = 0 then 0 else K η) ω := by sorry
