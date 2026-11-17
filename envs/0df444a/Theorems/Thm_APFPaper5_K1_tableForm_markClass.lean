-- Prove2me | Theorems.Thm_APFPaper5_K1_tableForm_markClass
-- name    : APFPaper5.K1.tableForm_markClass
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T17:42:07.69155+00:00
-- url     : https://prove2.me/theorems/8ea805b7-374a-4a10-9a06-0dbb85df08e3
-- title:
--   tableForm markClass
-- statement:
--   Result: tableForm markClass. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem tableForm_markClass (G : ι → ι → ℝ) (i j : ι) :
--       tableForm G (markClass i) (markClass j) = G i j
--   ```
--
--   Module context and limits: Given finite source data, nonnegative weights and SourceCounted, the party table has the displayed algebraic properties under identity role exchange. Mark classes and the exchange are supplied constructions; original physical readouts and full Paper 5 K1 coverage are not established.
--
--   Source scope parameters:
--
--   ```lean
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι]
--   variable {D P R Record : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
--     [Fintype Record]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_identity_exchange:60; pullbacks v39; source SHA-256 5c26600eda7b721f5defddee45946b97673ab369046eb093a904b83070e50125']

import Definitions.Def_APFPaper5_K1_identity_exchange_Vocabulary
import Theorems.Thm_APFPaper5_K1_sourceNeeds_mono
import Theorems.Thm_APFPaper5_K1_source_own_record_of_alone_not_rest
import Theorems.Thm_APFPaper5_K1_source_party_score_meets_K1
import Theorems.Thm_APFPaper5_K1_source_counted_family_meets_K1
import Theorems.Thm_APFPaper5_K1_leastBill_nonneg
import Theorems.Thm_APFPaper5_K1_leastBill_le_bill
import Theorems.Thm_APFPaper5_K1_le_leastBill
import Theorems.Thm_APFPaper5_K1_leastBill_pos_iff
import Theorems.Thm_APFPaper5_K1_source_counted_family_meets_K1_leastBill
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_sourceNeeds
import Theorems.Thm_APFPaper5_K1_cost_le_leastBill
import Theorems.Thm_APFPaper5_K1_leastBill_eq_cost_of_kept_alone
import Theorems.Thm_APFPaper5_K1_ledgerPartyScore_eq_source
import Theorems.Thm_APFPaper5_K1_counted_iff_sourceCounted
import Theorems.Thm_APFPaper5_K1_sourceCounted_leastBill_of_counted
import Theorems.Thm_APFPaper5_K1_PaidPair_source_counted_pair_meets_K1
import Theorems.Thm_APFPaper5_K1_exchanged_eq_ledger_add_orientation
import Theorems.Thm_APFPaper5_K1_ledgerForm_posDef
import Theorems.Thm_APFPaper5_K1_diagonal_parallelogram
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
set_option autoImplicit false
universe apfNative_u_1

theorem APFPaper5.K1.tableForm_markClass :
∀ {ι : Type apfNative_u_1} [inst : Fintype.{apfNative_u_1} ι] [inst_1 : DecidableEq.{apfNative_u_1 + 1} ι]
  (G : ι → ι → Real) (i j : ι),
  @Eq.{1} Real
    (@APFPaper5.K1.tableForm.{apfNative_u_1} ι inst G (@APFPaper5.K1.markClass.{apfNative_u_1} ι inst_1 i)
      (@APFPaper5.K1.markClass.{apfNative_u_1} ι inst_1 j))
    (G i j) := by sorry
