-- Prove2me | Theorems.Thm_APFPaper5_K1_hasOwnPaidRecord_of_available
-- name    : APFPaper5.K1.hasOwnPaidRecord_of_available
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T17:21:30.359542+00:00
-- url     : https://prove2.me/theorems/b2df11f8-57eb-481c-b599-306a6e8d3406
-- title:
--   hasOwnPaidRecord of available
-- statement:
--   Result: hasOwnPaidRecord of available. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem hasOwnPaidRecord_of_available [DecidableEq Record] (L : RecordLedger D P Record)
--       (tested : D → Prop) (C eps : ℝ)
--       (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
--         (R := fun _ => Finset Record) (Record := fun _ => Record) (fun _ => L.wholeResource)
--         (fun _ => L.calibration) (fun _ => L.maintained) (fun _ => L.sufficient)
--         (fun _ => L.usesToRealize) (fun _ => tested) (fun _ => C) (fun _ => eps))
--       (havail : LedgerAvailable L C) (dist : ι → D) (hcounted : LedgerCounted L tested C dist) :
--       HasOwnPaidRecord L dist
--   ```
--
--   Module context and limits: Counted explicitly includes own paid records and gives a faithful nonnegative diagonal on a finite record type. Deriving it from LedgerCounted additionally requires the declared marginal floor and LedgerAvailable. FreePair and Twins fail this stronger definition.
--
--   Source scope parameters:
--
--   ```lean
--   variable {D P Record : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_counted_family:54; pullbacks v39; source SHA-256 1516b4a976fe16e975b9aecfb11d8c455ad72d97076ec2ad17d2e8501c8b7e57']

import Definitions.Def_APFPaper5_K1_Counted
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Definitions.Def_APFPaper5_K1_free_pair_paid_relation_Vocabulary
import Theorems.Thm_APFPaper5_K1_FreePair_b05_holds
import Theorems.Thm_APFPaper5_K1_FreePair_pair_is_counted
import Theorems.Thm_APFPaper5_K1_FreePair_party_score_not_faithful
import Theorems.Thm_APFPaper5_K1_FreePair_no_own_paid_record
import Definitions.Def_APFPaper5_K1_twins_same_records_Vocabulary
import Theorems.Thm_APFPaper5_K1_Twins_fc_single
import Theorems.Thm_APFPaper5_K1_Twins_b05_holds
import Theorems.Thm_APFPaper5_K1_Twins_single_novel_over_empty
import Theorems.Thm_APFPaper5_K1_Twins_pair_is_counted
import Theorems.Thm_APFPaper5_K1_Twins_party_all
import Theorems.Thm_APFPaper5_K1_Twins_party_score_not_faithful
import Definitions.Def_APFPaper5_K1_counted_pair_with_relation_Vocabulary
import Theorems.Thm_APFPaper5_K1_PaidPair_b05_holds
import Theorems.Thm_APFPaper5_K1_PaidPair_pair_is_counted
import Theorems.Thm_APFPaper5_K1_PaidPair_relation_is_joint
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4

theorem APFPaper5.K1.hasOwnPaidRecord_of_available :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3} {ι : Type apfNative_u_4}
  [inst : Fintype.{apfNative_u_4} ι] [inst_1 : DecidableEq.{apfNative_u_4 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : DecidableEq.{apfNative_u_3 + 1} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (tested : D → Prop)
  (C eps : Real)
  (hB05 :
    @APFB05.MarginalFloor.{0, apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_3} Unit (fun (x : Unit) => D)
      (fun (x : Unit) => P) (fun (x : Unit) => Finset.{apfNative_u_3} Record) (fun (x : Unit) => Record)
      (fun (g : Unit) => inst_2)
      (fun (x : Unit) =>
        @APFPaper1.RecordLedger.wholeResource.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.calibration.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.maintained.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.sufficient.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) =>
        @APFPaper1.RecordLedger.usesToRealize.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => tested) (fun (x : Unit) => C) fun (x : Unit) => eps)
  (havail : @APFPaper5.K1.LedgerAvailable.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record inst_3 L C)
  (dist : ι → D)
  (hcounted :
    @APFPaper5.K1.LedgerCounted.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst inst_1
      inst_2 L tested C dist),
  @APFPaper5.K1.HasOwnPaidRecord.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst inst_1
    inst_2 L dist := by sorry
