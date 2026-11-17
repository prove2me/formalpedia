-- Prove2me | Theorems.Thm_APFPaper5_K1_ledgerPartyScore_eq_source
-- name    : APFPaper5.K1.ledgerPartyScore_eq_source
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:31:56.291443+00:00
-- url     : https://prove2.me/theorems/632eb601-2c8c-4f58-8921-1ef6d7c690b4
-- title:
--   ledgerPartyScore eq source
-- statement:
--   Result: ledgerPartyScore eq source. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem ledgerPartyScore_eq_source [Fintype Record] (L : RecordLedger D P Record) (dist : ι → D) :
--       ledgerPartyScore L dist =
--         sourcePartyScore (fun a => ((L.cost a : NNReal) : ℝ)) L.maintained L.sufficient
--           L.usesToRealize dist
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
--   ['Theorems.Thm_APFPaper5_K1_on_source_data:277; pullbacks v39; source SHA-256 6ca5d9b66c50938e503e99cb664a99b1add8b80f418492260dbb096c787f5371']

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
universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4

theorem APFPaper5.K1.ledgerPartyScore_eq_source :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3} {ι : Type apfNative_u_4}
  [inst : Fintype.{apfNative_u_4} ι] [inst_1 : DecidableEq.{apfNative_u_4 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : Fintype.{apfNative_u_3} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (dist : ι → D),
  @Eq.{apfNative_u_4 + 1} ((i j : ι) → Real)
    (@APFPaper5.K1.ledgerPartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst
      inst_1 inst_2 inst_3 L dist)
    (@APFPaper5.K1.sourcePartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst
      inst_1 inst_2 inst_3
      (fun (a : Record) =>
        NNReal.toReal (@APFPaper1.RecordLedger.cost.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L a))
      (@APFPaper1.RecordLedger.maintained.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (@APFPaper1.RecordLedger.sufficient.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (@APFPaper1.RecordLedger.usesToRealize.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L) dist) := by sorry
