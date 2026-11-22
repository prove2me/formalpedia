-- Prove2me | Theorems.Thm_APFPaper5_K2_keptClass_cost_r2
-- name    : APFPaper5.K2.keptClass_cost_r2
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T15:53:03.971313+00:00
-- url     : https://prove2.me/theorems/c1430ae1-d692-48fe-911a-f99c4e6b430b
-- title:
--   keptClass cost
-- statement:
--   Scope and conditions: The indicator square identity yields equality between weighted self-overlap and kept-record cost. Additivity for a union assumes both the union's Boolean keep rule and disjointness of the kept records. These unchanged theorems are moved from the prior state-class-candidates source to their own module. They select no physical state representation, and make no positive-definiteness claim.
--
--   Exact source statement:
--
--   theorem keptClass_cost [Fintype W] (w : W → ℝ) (keeps : Finset D → W → Bool) (S : Finset D) :
--       recordForm w (keptClass keeps S) (keptClass keeps S) = keptCost w keeps S
--
--   Source parameters:
--
--   universe uI uX uD uW
--   variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_kept_class_cost:137; USB pullbacks v58 batch B; SHA-256 737e8652c26e78691b1a9eaef5ebb65e46928500d93f1e3fc6c7bfa0a8798623']

import Definitions.Def_APFPaper5_K2_RecordedClass
import Definitions.Def_APFPaper5_K1_PartyScore
set_option autoImplicit false
universe apfNative_uD apfNative_uW

theorem APFPaper5.K2.keptClass_cost_r2 :
∀ {D : Type apfNative_uD} {W : Type apfNative_uW} [inst : Fintype.{apfNative_uW} W] (w : W → Real)
  (keeps : Finset.{apfNative_uD} D → W → Bool) (S : Finset.{apfNative_uD} D),
  @Eq.{1} Real
    (@APFPaper5.K2.recordForm.{apfNative_uW} W inst w (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S)
      (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S))
    (@APFPaper5.K1.keptCost.{apfNative_uD, apfNative_uW} D W inst w keeps S) := by sorry
