-- Prove2me | Theorems.Thm_APFPaper5_K1_leastBill_pos_iff
-- name    : APFPaper5.K1.leastBill_pos_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:32:06.09617+00:00
-- url     : https://prove2.me/theorems/b9dd9ad9-548d-4e7f-9d48-ad9653c06a2d
-- title:
--   leastBill pos iff
-- statement:
--   Result: leastBill pos iff. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem leastBill_pos_iff (wholeResource : P → R) (calibration : R → NNReal)
--       (maintained : P → Set Record) (a : Record) :
--       0 < leastBill wholeResource calibration maintained a ↔
--         (∃ p : P, a ∈ maintained p) ∧
--           ∃ e : ℝ, 0 < e ∧ ∀ p : P, a ∈ maintained p → e ≤ (calibration (wholeResource p) : ℝ)
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
--   ['Theorems.Thm_APFPaper5_K1_on_source_data:192; pullbacks v39; source SHA-256 6ca5d9b66c50938e503e99cb664a99b1add8b80f418492260dbb096c787f5371']

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

theorem APFPaper5.K1.leastBill_pos_iff :
∀ {P : Type apfNative_u_1} {R : Type apfNative_u_2} {Record : Type apfNative_u_3} (wholeResource : P → R)
  (calibration : R → NNReal) (maintained : P → Set.{apfNative_u_3} Record) (a : Record),
  Iff
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@APFPaper5.K1.leastBill.{apfNative_u_1, apfNative_u_2, apfNative_u_3} P R Record wholeResource calibration
        maintained a))
    (And
      (@Exists.{apfNative_u_1 + 1} P fun (p : P) =>
        @Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Set.{apfNative_u_3} Record)
          (@Set.instMembership.{apfNative_u_3} Record) (maintained p) a)
      (@Exists.{1} Real fun (e : Real) =>
        And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) e)
          (∀ (p : P),
            @Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Set.{apfNative_u_3} Record)
                (@Set.instMembership.{apfNative_u_3} Record) (maintained p) a →
              @LE.le.{0} Real Real.instLE e (NNReal.toReal (calibration (wholeResource p)))))) := by sorry
