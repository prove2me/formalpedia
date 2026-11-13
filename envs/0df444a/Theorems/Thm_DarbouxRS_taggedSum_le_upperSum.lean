-- Prove2me | Theorems.Thm_DarbouxRS_taggedSum_le_upperSum
-- name    : DarbouxRS.taggedSum_le_upperSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T08:05:36.080903+00:00
-- url     : https://prove2.me/theorems/22e29e0f-5cc8-43cf-b696-7da72aabd850
-- title:
--   Chapter 1, thm_1_2: DarbouxRS.taggedSum_le_upperSum
-- statement:
--   Source theorem `DarbouxRS.taggedSum_le_upperSum` from Chapter 1, module `thm_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F007
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

theorem taggedSum_le_upperSum {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    taggedSum P tags f alpha ≤ upperSum P f alpha := by sorry

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result
