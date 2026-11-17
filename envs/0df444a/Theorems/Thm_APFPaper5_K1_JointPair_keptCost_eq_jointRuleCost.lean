-- Prove2me | Theorems.Thm_APFPaper5_K1_JointPair_keptCost_eq_jointRuleCost
-- name    : APFPaper5.K1.JointPair.keptCost_eq_jointRuleCost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:15:30.234503+00:00
-- url     : https://prove2.me/theorems/65dfbdb3-a72a-4b30-9e1e-50ff57d5084c
-- title:
--   keptCost eq jointRuleCost
-- statement:
--   Result: keptCost eq jointRuleCost. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem keptCost_eq_jointRuleCost : keptCost w (keepsB mark joint) = jointRuleCost
--   ```
--
--   Module context and limits: The three-record example has family costs 0,1,1,3, a faithful party score and a degenerate shared-cost table. It is a book with no asserted states, continuations or satisfaction of all eight forms.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_party_score_joint_pair:33; pullbacks v39; source SHA-256 29586b17fa1fd9cde9073a56d5b1c3cff8d1799cfa78be60d8eff0203e3af4f7']

import Definitions.Def_APFPaper5_K1_party_score_joint_pair_Vocabulary
import Theorems.Thm_APFPaper5_K1_partyTo_book_iff
import Theorems.Thm_APFPaper5_K1_partyScore_book
import Theorems.Thm_APFPaper5_K1_partyScore_book_meets_K1
import Theorems.Thm_APFPaper5_K1_partyScore_book_faithful_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_eq_partyScore_of_no_joint
import Definitions.Def_APFPaper5_K1_joint_pair_two_tables_Vocabulary
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_empty
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_zero
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_one
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_univ
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_sharedCost_table_not_faithful

set_option autoImplicit false

namespace APFPaper5.K1.JointPair
end APFPaper5.K1.JointPair
open APFPaper5
open APFPaper5.K1
open APFPaper5.K1.JointPair

theorem APFPaper5.K1.JointPair.keptCost_eq_jointRuleCost : keptCost w (keepsB mark joint) = jointRuleCost := by sorry
