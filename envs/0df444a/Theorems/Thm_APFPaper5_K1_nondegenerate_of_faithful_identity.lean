-- Prove2me | Theorems.Thm_APFPaper5_K1_nondegenerate_of_faithful_identity
-- name    : APFPaper5.K1.nondegenerate_of_faithful_identity
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T17:42:04.805366+00:00
-- url     : https://prove2.me/theorems/59eaef37-8085-480e-9219-cd5c04b8ea20
-- title:
--   nondegenerate of faithful identity
-- statement:
--   Result: nondegenerate of faithful identity. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   omit [DecidableEq ι] in
--
--   theorem nondegenerate_of_faithful_identity (G : ι → ι → ℝ)
--       (h : FaithfulNonnegDiagonal (tableForm G) (LinearEquiv.refl ℝ (ι → ℝ))) :
--       IsNondegenerate (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G)
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
--   ['Theorems.Thm_APFPaper5_K1_identity_exchange:83; pullbacks v39; source SHA-256 5c26600eda7b721f5defddee45946b97673ab369046eb093a904b83070e50125']

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

theorem APFPaper5.K1.nondegenerate_of_faithful_identity :
∀ {ι : Type apfNative_u_1} [inst : Fintype.{apfNative_u_1} ι] (G : ι → ι → Real)
  (h :
    @APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u_1, apfNative_u_1} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_1, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_1, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_1, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_1, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_1} ι inst G)
      (@LinearEquiv.refl.{0, apfNative_u_1} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u_1, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u_1, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))),
  @APFPaper5.K1.IsNondegenerate.{apfNative_u_1, apfNative_u_1} (ι → Real) (ι → Real)
    (@Pi.addCommGroup.{apfNative_u_1, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
    (@Pi.addCommGroup.{apfNative_u_1, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
    (@APFPaper5.K1.tableForm.{apfNative_u_1} ι inst G) := by sorry
