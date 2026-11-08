-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_rightlimit
-- name    : AvramDividend.Classical.avram_e0_initial_only_dividend_rightlimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:06:28.31107+00:00
-- url     : https://prove2.me/theorems/7fa270ec-4435-449c-89f2-449ed15689b7
-- title:
--   A dividend paid immediately after zero and held constant has the same right limit at every time
-- statement:
--   The original Avram dividend right-limit infimum of an initial-only dividend step equals its post-origin level at every nonnegative clock, including zero. This is a source-exact stepping stone from an independent geometric reserve mark to the original uniform-grid row zero.
-- source:
--   Published original dividend strategy definition and necessary geometric initial-mark construction for e0b94d7f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_only_dividend_rightlimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (K : Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    rightLimit (fun s ω => if s = 0 then 0 else K ω) t ω = K ω := by sorry
