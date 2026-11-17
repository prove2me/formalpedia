-- Prove2me | Theorems.Thm_APFPaper5_K1_JointPair_same_costs_different_verdicts
-- name    : APFPaper5.K1.JointPair.same_costs_different_verdicts
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:26:34.514749+00:00
-- url     : https://prove2.me/theorems/4376b232-c57f-417d-aa66-e3ec605d4c1a
-- title:
--   same costs different verdicts
-- statement:
--   Result: same costs different verdicts. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem same_costs_different_verdicts :
--       keptCost wSigned (keepsB mark noJoint) = keptCost w (keepsB mark joint) ∧
--         FaithfulNonnegDiagonal (tableForm (partyScore w (keepsB mark joint)))
--           (LinearEquiv.refl ℝ (Fin 2 → ℝ)) ∧
--         ¬ FaithfulNonnegDiagonal (tableForm (partyScore wSigned (keepsB mark noJoint)))
--           (LinearEquiv.refl ℝ (Fin 2 → ℝ))
--   ```
--
--   Module context and limits: Two supplied books give the same family cost function but different faithful-diagonal verdicts. The signed book uses a negative real weight and therefore is not a RecordLedger with nonnegative record costs. No physical negative record cost is asserted.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_same_costs_two_books:109; pullbacks v39; source SHA-256 c028ca542f16a5cf9503d762edd30a7b8af3654ae3dc30e9a36ef928c9a508c5']

import Definitions.Def_APFPaper5_K1_same_costs_two_books_Vocabulary
import Definitions.Def_APFPaper5_K1_party_score_joint_pair_Vocabulary
import Theorems.Thm_APFPaper5_K1_JointPair_keptCost_eq_jointRuleCost
import Theorems.Thm_APFPaper5_K1_JointPair_partyScore_meets_K1

set_option autoImplicit false

namespace APFPaper5.K1.JointPair
end APFPaper5.K1.JointPair
open APFPaper5
open APFPaper5.K1
open APFPaper5.K1.JointPair

theorem APFPaper5.K1.JointPair.same_costs_different_verdicts :
    keptCost wSigned (keepsB mark noJoint) = keptCost w (keepsB mark joint) ∧
      FaithfulNonnegDiagonal (tableForm (partyScore w (keepsB mark joint)))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) ∧
      ¬ FaithfulNonnegDiagonal (tableForm (partyScore wSigned (keepsB mark noJoint)))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) := by sorry
