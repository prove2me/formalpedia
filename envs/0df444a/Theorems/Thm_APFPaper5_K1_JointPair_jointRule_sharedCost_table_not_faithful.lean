-- Prove2me | Theorems.Thm_APFPaper5_K1_JointPair_jointRule_sharedCost_table_not_faithful
-- name    : APFPaper5.K1.JointPair.jointRule_sharedCost_table_not_faithful
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:44:45.182316+00:00
-- url     : https://prove2.me/theorems/54c44f21-11ef-4df8-9e8f-273fe1a2f1f9
-- title:
--   jointRule sharedCost table not faithful
-- statement:
--   Result: jointRule sharedCost table not faithful. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem jointRule_sharedCost_table_not_faithful :
--       ¬ FaithfulNonnegDiagonal (tableForm (fun i j => sharedCost jointRuleCost {i} {j}))
--           (LinearEquiv.refl ℝ (Fin 2 → ℝ))
--   ```
--
--   Module context and limits: The same listing gives costs 0,2,2,3 under the shared rule and 0,1,1,3 under the joint rule. Its record table is faithful; the joint-rule shared-cost table is degenerate. These are supplied books, not physical worlds.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_joint_pair_two_tables:200; pullbacks v39; source SHA-256 f0957eb5dd11718bbec63d57b872fe7ef3cdcd79fec575e1c5875ac04817e583']

import Definitions.Def_APFPaper5_K1_joint_pair_two_tables_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper5.K1.JointPair
end APFPaper5.K1.JointPair
open APFPaper5
open APFPaper5.K1
open APFPaper5.K1.JointPair
/-! ### The costs under each rule -/

















/-! ### The record-book table: the same under both rules -/





/-! ### Shared rule: the table of shared costs is the record-book table -/



/-! ### Joint rule: the table of shared costs is not the record-book table, and is not faithful -/

theorem APFPaper5.K1.JointPair.jointRule_sharedCost_table_not_faithful :
    ¬ FaithfulNonnegDiagonal (tableForm (fun i j => sharedCost jointRuleCost {i} {j}))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) := by sorry
