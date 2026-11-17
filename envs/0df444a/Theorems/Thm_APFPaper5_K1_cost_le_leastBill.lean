-- Prove2me | Theorems.Thm_APFPaper5_K1_cost_le_leastBill
-- name    : APFPaper5.K1.cost_le_leastBill
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:31:53.574005+00:00
-- url     : https://prove2.me/theorems/1b54361a-3d92-4006-a86c-a3503f93e66c
-- title:
--   cost le leastBill
-- statement:
--   Result: cost le leastBill. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem cost_le_leastBill (L : RecordLedger D P Record) (a : Record) (hne : ∃ p : P, a ∈ L.kept p) :
--       ((L.cost a : NNReal) : ℝ) ≤ leastBill L.wholeResource L.calibration L.maintained a
--   ```
--
--   Module context and limits: Theorems retain the supplied support predicates, finite record type, nonnegative weights and own-record or SourceCounted hypotheses. leastBill remains an unruled candidate with empty real infimum zero. Ledger specialization is proved without asserting all source bills are additive.
--
--   Source scope parameters:
--
--   ```lean
--   variable {D P R Record : Type*}
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
--   variable [Fintype Record]
--   variable {P R Record : Type*}
--   variable {D : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D] [Fintype Record]
--   variable {D P Record : Type*}
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_on_source_data:251; pullbacks v39; source SHA-256 6ca5d9b66c50938e503e99cb664a99b1add8b80f418492260dbb096c787f5371']

import Definitions.Def_APFPaper5_K1_SourcePartyScore
import Definitions.Def_APFPaper5_K1_Counted
import Theorems.Thm_APFPaper5_K1_partyScore_meets_K1_of_own_record
import Theorems.Thm_APFPaper5_K1_memberNeeds_subset_familyNeeds_explicit
import Theorems.Thm_APFPaper5_K1_familyNeeds_eq_of_exactly_served_explicit
import Theorems.Thm_APFPaper5_K1_ledger_party_score_meets_K1_explicit
import Theorems.Thm_APFPaper5_K1_ledger_counted_family_party_score_satisfies_K1_explicit
import Definitions.Def_APFPaper5_K1_counted_pair_with_relation_Vocabulary
import Theorems.Thm_APFPaper5_K1_PaidPair_b05_holds
import Theorems.Thm_APFPaper5_K1_PaidPair_pair_is_counted
import Theorems.Thm_APFPaper5_K1_PaidPair_relation_is_joint
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2 apfNative_u_3

theorem APFPaper5.K1.cost_le_leastBill :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3}
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (a : Record)
  (hne :
    @Exists.{apfNative_u_2 + 1} P fun (p : P) =>
      @Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Finset.{apfNative_u_3} Record)
        (@SetLike.instMembership.{apfNative_u_3, apfNative_u_3} (Finset.{apfNative_u_3} Record) Record
          (@Finset.instSetLike.{apfNative_u_3} Record))
        (@APFPaper1.RecordLedger.kept.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L p) a),
  @LE.le.{0} Real Real.instLE
    (NNReal.toReal (@APFPaper1.RecordLedger.cost.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L a))
    (@APFPaper5.K1.leastBill.{apfNative_u_2, apfNative_u_3, apfNative_u_3} P (Finset.{apfNative_u_3} Record) Record
      (@APFPaper1.RecordLedger.wholeResource.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (@APFPaper1.RecordLedger.calibration.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (@APFPaper1.RecordLedger.maintained.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L) a) := by sorry
