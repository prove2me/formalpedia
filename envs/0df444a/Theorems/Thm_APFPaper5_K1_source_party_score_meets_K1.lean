-- Prove2me | Theorems.Thm_APFPaper5_K1_source_party_score_meets_K1
-- name    : APFPaper5.K1.source_party_score_meets_K1
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T17:28:09.834504+00:00
-- url     : https://prove2.me/theorems/01f35bef-75fa-41fa-915e-f8c2ff548d52
-- title:
--   source party score meets K1
-- statement:
--   Result: source party score meets K1. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem source_party_score_meets_K1 (w : Record → ℝ) (hw : ∀ a, 0 ≤ w a)
--       (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
--       (usesToRealize : P → D → Set Record → Prop) (dist : ι → D)
--       (hown : SourceHasOwnPaidRecord w maintained sufficient usesToRealize dist) :
--       IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
--           (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist)) ∧
--         FaithfulNonnegDiagonal
--           (tableForm (sourcePartyScore w maintained sufficient usesToRealize dist))
--           (LinearEquiv.refl ℝ (ι → ℝ))
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
--   ['Theorems.Thm_APFPaper5_K1_on_source_data:119; pullbacks v39; source SHA-256 6ca5d9b66c50938e503e99cb664a99b1add8b80f418492260dbb096c787f5371']

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

theorem APFPaper5.K1.source_party_score_meets_K1 :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_4} {ι : Type apfNative_u_5}
  [inst : Fintype.{apfNative_u_5} ι] [inst_1 : DecidableEq.{apfNative_u_5 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : Fintype.{apfNative_u_4} Record] (w : Record → Real)
  (hw :
    ∀ (a : Record),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w a))
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (dist : ι → D)
  (hown :
    @APFPaper5.K1.SourceHasOwnPaidRecord.{apfNative_u_1, apfNative_u_2, apfNative_u_4, apfNative_u_5} D P Record ι inst
      inst_1 inst_2 w maintained sufficient usesToRealize dist),
  And
    (@APFPaper5.K1.IsBilinear.{apfNative_u_5, apfNative_u_5} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_5} ι inst
        (@APFPaper5.K1.sourcePartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_4, apfNative_u_5} D P Record ι inst
          inst_1 inst_2 inst_3 w maintained sufficient usesToRealize dist)))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u_5, apfNative_u_5} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_5} ι inst
        (@APFPaper5.K1.sourcePartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_4, apfNative_u_5} D P Record ι inst
          inst_1 inst_2 inst_3 w maintained sufficient usesToRealize dist))
      (@LinearEquiv.refl.{0, apfNative_u_5} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by sorry
