-- Prove2me | Theorems.Thm_DarbouxRS_lowerSum_le_taggedSum
-- name    : DarbouxRS.lowerSum_le_taggedSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T08:04:49.82919+00:00
-- url     : https://prove2.me/theorems/b95740b9-b79f-4580-8d76-0837d50c63c8
-- title:
--   Chapter 1, thm_1_2: DarbouxRS.lowerSum_le_taggedSum
-- statement:
--   Source theorem `DarbouxRS.lowerSum_le_taggedSum` from Chapter 1, module `thm_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F006
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

theorem lowerSum_le_taggedSum {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f alpha ≤ taggedSum P tags f alpha := by sorry

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result
