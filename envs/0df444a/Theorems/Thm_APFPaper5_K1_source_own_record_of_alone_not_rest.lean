-- Prove2me | Theorems.Thm_APFPaper5_K1_source_own_record_of_alone_not_rest
-- name    : APFPaper5.K1.source_own_record_of_alone_not_rest
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T17:28:15.925197+00:00
-- url     : https://prove2.me/theorems/1364e86e-40cd-4b5b-a55c-2446be5ec0c4
-- title:
--   source own record of alone not rest
-- statement:
--   Result: source own record of alone not rest. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem source_own_record_of_alone_not_rest (maintained : P → Set Record)
--       (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
--       (dist : ι → D) (i : ι) (a : Record)
--       (halone : a ∈ sourceNeeds maintained sufficient usesToRealize {dist i})
--       (hrest : a ∉ sourceNeeds maintained sufficient usesToRealize ((Finset.univ.erase i).image dist)) :
--       PartyTo (sourceKeeps maintained sufficient usesToRealize dist) i a ∧
--         ∀ j, PartyTo (sourceKeeps maintained sufficient usesToRealize dist) j a → j = i
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
--   ['Theorems.Thm_APFPaper5_K1_on_source_data:78; pullbacks v39; source SHA-256 6ca5d9b66c50938e503e99cb664a99b1add8b80f418492260dbb096c787f5371']

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
universe apfNative_u_1 apfNative_u_2 apfNative_u_4 apfNative_u_5

theorem APFPaper5.K1.source_own_record_of_alone_not_rest :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_4} {ι : Type apfNative_u_5}
  [inst : Fintype.{apfNative_u_5} ι] [inst_1 : DecidableEq.{apfNative_u_5 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] (maintained : P → Set.{apfNative_u_4} Record)
  (sufficient : P → Set.{apfNative_u_4} Record → D → Prop) (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop)
  (dist : ι → D) (i : ι) (a : Record)
  (halone :
    @Membership.mem.{apfNative_u_4, apfNative_u_4} Record (Set.{apfNative_u_4} Record)
      (@Set.instMembership.{apfNative_u_4} Record)
      (@APFPaper5.K1.sourceNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
        usesToRealize
        (@Singleton.singleton.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
          (@Finset.instSingleton.{apfNative_u_1} D) (dist i)))
      a)
  (hrest :
    Not
      (@Membership.mem.{apfNative_u_4, apfNative_u_4} Record (Set.{apfNative_u_4} Record)
        (@Set.instMembership.{apfNative_u_4} Record)
        (@APFPaper5.K1.sourceNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
          usesToRealize
          (@Finset.image.{apfNative_u_5, apfNative_u_1} ι D inst_2 dist
            (@Finset.erase.{apfNative_u_5} ι inst_1 (@Finset.univ.{apfNative_u_5} ι inst) i)))
        a)),
  And
    (@APFPaper5.K1.PartyTo.{apfNative_u_5, apfNative_u_4} ι Record inst_1
      (@APFPaper5.K1.sourceKeeps.{apfNative_u_1, apfNative_u_2, apfNative_u_4, apfNative_u_5} D P Record ι inst_2
        maintained sufficient usesToRealize dist)
      i a)
    (∀ (j : ι),
      @APFPaper5.K1.PartyTo.{apfNative_u_5, apfNative_u_4} ι Record inst_1
          (@APFPaper5.K1.sourceKeeps.{apfNative_u_1, apfNative_u_2, apfNative_u_4, apfNative_u_5} D P Record ι inst_2
            maintained sufficient usesToRealize dist)
          j a →
        @Eq.{apfNative_u_5 + 1} ι j i) := by sorry
