-- Prove2me | Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint_r2
-- name    : APFPaper5.K2.keptClass_union_of_disjoint_r2
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T15:54:29.498446+00:00
-- url     : https://prove2.me/theorems/f266d033-0df2-454f-a150-52b1ff07047d
-- title:
--   keptClass union of disjoint
-- statement:
--   Scope and conditions: The indicator square identity yields equality between weighted self-overlap and kept-record cost. Additivity for a union assumes both the union's Boolean keep rule and disjointness of the kept records. These unchanged theorems are moved from the prior state-class-candidates source to their own module. They select no physical state representation, and make no positive-definiteness claim.
--
--   Exact source statement:
--
--   theorem keptClass_union_of_disjoint [DecidableEq D] (keeps : Finset D → W → Bool)
--       (S T : Finset D) (hunion : ∀ a, keeps (S ∪ T) a = (keeps S a || keeps T a))
--       (hdisj : ∀ a, ¬ (keeps S a = true ∧ keeps T a = true)) :
--       keptClass keeps (S ∪ T) = keptClass keeps S + keptClass keeps T
--
--   Source parameters:
--
--   universe uI uX uD uW
--   variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_kept_class_cost:144; USB pullbacks v58 batch B; SHA-256 737e8652c26e78691b1a9eaef5ebb65e46928500d93f1e3fc6c7bfa0a8798623']

import Definitions.Def_APFPaper5_K2_RecordedClass
import Definitions.Def_APFPaper5_K1_PartyScore
set_option autoImplicit false
universe apfNative_uD apfNative_uW

theorem APFPaper5.K2.keptClass_union_of_disjoint_r2 :
∀ {D : Type apfNative_uD} {W : Type apfNative_uW} [inst : DecidableEq.{apfNative_uD + 1} D]
  (keeps : Finset.{apfNative_uD} D → W → Bool) (S T : Finset.{apfNative_uD} D)
  (hunion :
    ∀ (a : W),
      @Eq.{1} Bool
        (keeps (@Union.union.{apfNative_uD} (Finset.{apfNative_uD} D) (@Finset.instUnion.{apfNative_uD} D inst) S T) a)
        (Bool.or (keeps S a) (keeps T a)))
  (hdisj : ∀ (a : W), Not (And (@Eq.{1} Bool (keeps S a) Bool.true) (@Eq.{1} Bool (keeps T a) Bool.true))),
  @Eq.{apfNative_uW + 1} (W → Real)
    (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps
      (@Union.union.{apfNative_uD} (Finset.{apfNative_uD} D) (@Finset.instUnion.{apfNative_uD} D inst) S T))
    (@HAdd.hAdd.{apfNative_uW, apfNative_uW, apfNative_uW} (W → Real) (W → Real) (W → Real)
      (@instHAdd.{apfNative_uW} (W → Real)
        (@Pi.instAdd.{apfNative_uW, 0} W (fun (a : W) => Real) fun (i : W) => Real.instAdd))
      (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S)
      (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps T)) := by sorry
