-- Prove2me | Theorems.Thm_APFPaper1_Continuation_Reference_prefix_restriction_not_automatic
-- name    : APFPaper1.Continuation.Reference.prefix_restriction_not_automatic
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:17:14.234973+00:00
-- url     : https://prove2.me/theorems/79586339-42c8-41b2-b95b-48cb22147c98
-- title:
--   Whole-word admissibility need not pass to a prefix
-- statement:
--   The model has one raw state and one fragment, and permits every step. Resource is word length, while calibration charges two at length one and zero otherwise. This calibration is not asserted to be physically monotone. The example separates two definitions and supplies no physical resource counterexample. In the explicit one-context model, the one-letter word is a prefix of the two-letter word. The two-letter word belongs to the whole-word continuation class, while the one-letter word does not: their bills are respectively zero and two, and capacity is one. Thus the whole-word definition alone does not force prefix admissibility. Source: Sib v15 explicit countermodel; November 12 continuation ruling, conditional C3.
-- source:
--   Reference/Ref_APFPaper1_Cont_prefix_countermodel.lean, declaration at line 43 (Sib v15; source-scoped review). Sib v15 explicit countermodel; November 12 continuation ruling, conditional C3.

import Definitions.Def_APFPaper1_Cont_prefix_countermodel_data
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation.Reference
open APFPaper1.Continuation

theorem APFPaper1.Continuation.Reference.prefix_restriction_not_automatic :
    IsPrefix one two ∧
      Cont step resource calibration capacity () () two ∧
      ¬ Cont step resource calibration capacity () () one := by sorry
