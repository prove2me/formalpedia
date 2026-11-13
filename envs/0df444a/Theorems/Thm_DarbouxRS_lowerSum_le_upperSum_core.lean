-- Prove2me | Theorems.Thm_DarbouxRS_lowerSum_le_upperSum_core
-- name    : DarbouxRS.lowerSum_le_upperSum_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T15:32:21.172678+00:00
-- url     : https://prove2.me/theorems/7e5bf83e-2206-492a-88cb-2339b9223cba
-- title:
--   Chapter 1, thm_1_2: DarbouxRS.lowerSum_le_upperSum_core
-- statement:
--   Source theorem `DarbouxRS.lowerSum_le_upperSum_core` from Chapter 1, module `thm_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

theorem lowerSum_le_upperSum_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) :
    lowerSum P f alpha ≤ upperSum P f alpha := by sorry

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result
