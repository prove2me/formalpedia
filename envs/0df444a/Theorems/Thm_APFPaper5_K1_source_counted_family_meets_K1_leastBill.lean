-- Prove2me | Theorems.Thm_APFPaper5_K1_source_counted_family_meets_K1_leastBill
-- name    : APFPaper5.K1.source_counted_family_meets_K1_leastBill
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T17:28:13.091191+00:00
-- url     : https://prove2.me/theorems/188bdbc6-b16f-446d-b523-333a5882c271
-- title:
--   source counted family meets K1 leastBill
-- statement:
--   Result: source counted family meets K1 leastBill. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem source_counted_family_meets_K1_leastBill (wholeResource : P → R) (calibration : R → NNReal)
--       (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
--       (usesToRealize : P → D → Set Record → Prop) (tested : D → Prop) (C : ℝ) (dist : ι → D)
--       (h : SourceCounted (leastBill wholeResource calibration maintained) wholeResource calibration
--         maintained sufficient usesToRealize tested C dist) :
--       IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
--           (tableForm (sourcePartyScore (leastBill wholeResource calibration maintained) maintained
--             sufficient usesToRealize dist)) ∧
--         FaithfulNonnegDiagonal
--           (tableForm (sourcePartyScore (leastBill wholeResource calibration maintained) maintained
--             sufficient usesToRealize dist))
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
--   ['Theorems.Thm_APFPaper5_K1_on_source_data:222; pullbacks v39; source SHA-256 6ca5d9b66c50938e503e99cb664a99b1add8b80f418492260dbb096c787f5371']

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
universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5

theorem APFPaper5.K1.source_counted_family_meets_K1_leastBill :
∀ {P : Type apfNative_u_1} {R : Type apfNative_u_2} {Record : Type apfNative_u_3} {D : Type apfNative_u_4}
  {ι : Type apfNative_u_5} [inst : Fintype.{apfNative_u_5} ι] [inst_1 : DecidableEq.{apfNative_u_5 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_4 + 1} D] [inst_3 : Fintype.{apfNative_u_3} Record] (wholeResource : P → R)
  (calibration : R → NNReal) (maintained : P → Set.{apfNative_u_3} Record)
  (sufficient : P → Set.{apfNative_u_3} Record → D → Prop) (usesToRealize : P → D → Set.{apfNative_u_3} Record → Prop)
  (tested : D → Prop) (C : Real) (dist : ι → D)
  (h :
    @APFPaper5.K1.SourceCounted.{apfNative_u_4, apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_5} D P R Record
      ι inst inst_1 inst_2
      (@APFPaper5.K1.leastBill.{apfNative_u_1, apfNative_u_2, apfNative_u_3} P R Record wholeResource calibration
        maintained)
      wholeResource calibration maintained sufficient usesToRealize tested C dist),
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
        (@APFPaper5.K1.sourcePartyScore.{apfNative_u_4, apfNative_u_1, apfNative_u_3, apfNative_u_5} D P Record ι inst
          inst_1 inst_2 inst_3
          (@APFPaper5.K1.leastBill.{apfNative_u_1, apfNative_u_2, apfNative_u_3} P R Record wholeResource calibration
            maintained)
          maintained sufficient usesToRealize dist)))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u_5, apfNative_u_5} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_5} ι inst
        (@APFPaper5.K1.sourcePartyScore.{apfNative_u_4, apfNative_u_1, apfNative_u_3, apfNative_u_5} D P Record ι inst
          inst_1 inst_2 inst_3
          (@APFPaper5.K1.leastBill.{apfNative_u_1, apfNative_u_2, apfNative_u_3} P R Record wholeResource calibration
            maintained)
          maintained sufficient usesToRealize dist))
      (@LinearEquiv.refl.{0, apfNative_u_5} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u_5, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u_5, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by sorry
