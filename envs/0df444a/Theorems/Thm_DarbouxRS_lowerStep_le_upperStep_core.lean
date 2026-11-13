-- Prove2me | Theorems.Thm_DarbouxRS_lowerStep_le_upperStep_core
-- name    : DarbouxRS.lowerStep_le_upperStep_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:46:47.364552+00:00
-- url     : https://prove2.me/theorems/c341a738-762b-4474-892c-c9460f9d6eb6
-- title:
--   Chapter 1, thm_1_2: DarbouxRS.lowerStep_le_upperStep_core
-- statement:
--   Source theorem `DarbouxRS.lowerStep_le_upperStep_core` from Chapter 1, module `thm_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

theorem lowerStep_le_upperStep_core {a b : ℝ} (P : Partition a b)
    {f : ℝ → ℝ} (i : Fin P.n)
    (hBelow : BddBelow (f '' Set.Icc a b))
    (hAbove : BddAbove (f '' Set.Icc a b)) :
    lowerStep P f i ≤ upperStep P f i := by sorry

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result
