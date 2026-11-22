-- Prove2me | Theorems.Thm_APFPaper5_K2_ind_mul_self
-- name    : APFPaper5.K2.ind_mul_self
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:47:18.507833+00:00
-- url     : https://prove2.me/theorems/5999a419-726d-456b-9b75-0d7ea7f0ab68
-- title:
--   ind mul self
-- statement:
--   Scope and conditions: The indicator square identity yields equality between weighted self-overlap and kept-record cost. Additivity for a union assumes both the union's Boolean keep rule and disjointness of the kept records. These unchanged theorems are moved from the prior state-class-candidates source to their own module. They select no physical state representation, and make no positive-definiteness claim.
--
--   Exact source statement:
--
--   theorem ind_mul_self (b : Bool) : ind b * ind b = ind b
--
--   Source parameters:
--
--   universe uI uX uD uW
--   variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_kept_class_cost:132; USB pullbacks v58 batch B; SHA-256 737e8652c26e78691b1a9eaef5ebb65e46928500d93f1e3fc6c7bfa0a8798623']

import Definitions.Def_APFPaper5_K2_RecordedClass
import Definitions.Def_APFPaper5_K1_PartyScore
set_option autoImplicit false

theorem APFPaper5.K2.ind_mul_self :
∀ (b : Bool),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (APFPaper5.K1.ind b) (APFPaper5.K1.ind b))
    (APFPaper5.K1.ind b) := by sorry
