-- Prove2me | Theorems.Thm_APFPaper5_K1_counted_family_meets_K1
-- name    : APFPaper5.K1.counted_family_meets_K1
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:42:55.582789+00:00
-- url     : https://prove2.me/theorems/cd9a8630-8bf3-46b9-93f9-143dd313c058
-- title:
--   counted family meets K1
-- statement:
--   Result: counted family meets K1. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem counted_family_meets_K1 [Fintype Record] (L : RecordLedger D P Record) (tested : D → Prop)
--       (C : ℝ) (dist : ι → D) (h : Counted L tested C dist) :
--       IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (ledgerPartyScore L dist)) ∧
--         FaithfulNonnegDiagonal (tableForm (ledgerPartyScore L dist)) (LinearEquiv.refl ℝ (ι → ℝ))
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
--   ['Theorems.Thm_APFPaper5_K1_counted_family:47; pullbacks v39; source SHA-256 1516b4a976fe16e975b9aecfb11d8c455ad72d97076ec2ad17d2e8501c8b7e57']

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

theorem APFPaper5.K1.counted_family_meets_K1 :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3} {ι : Type apfNative_u_4}
  [inst : Fintype.{apfNative_u_4} ι] [inst_1 : DecidableEq.{apfNative_u_4 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : Fintype.{apfNative_u_3} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (tested : D → Prop) (C : Real)
  (dist : ι → D)
  (h :
    @APFPaper5.K1.Counted.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst inst_1 inst_2 L
      tested C dist),
  And
    (@APFPaper5.K1.IsBilinear.{apfNative_u_4, apfNative_u_4} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_4} ι inst
        (@APFPaper5.K1.ledgerPartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst
          inst_1 inst_2 inst_3 L dist)))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u_4, apfNative_u_4} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_4} ι inst
        (@APFPaper5.K1.ledgerPartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst
          inst_1 inst_2 inst_3 L dist))
      (@LinearEquiv.refl.{0, apfNative_u_4} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by sorry
