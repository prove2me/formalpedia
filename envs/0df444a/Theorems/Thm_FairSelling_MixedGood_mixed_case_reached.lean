-- Prove2me | Theorems.Thm_FairSelling_MixedGood_mixed_case_reached
-- name    : FairSelling.MixedGood.mixed_case_reached
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:54:35.68684+00:00
-- url     : https://prove2.me/theorems/bb2a8703-0e13-4df2-96a9-0da017547df3
-- title:
--   Mixed Good: mixed case reached
-- statement:
--   **The sharing case of Algorithm 6 is reached at the first step.**  At the initial stage of
--   Algorithm 6 on this instance the good `g₀` is in the pool and expensive for the unserved agent
--   `0`, it is not pure, and the pure moving knife cannot be run because there is no money in the
--   bank and no pure good to sell.  The only way forward is `PhaseTPS.pshare_step`: sell `g₀` and
--   hand out only part of its proceeds.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L172-L194
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L172-L194

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood

theorem FairSelling.MixedGood.mixed_case_reached (eps : ℝ) :
    (PhaseTPS.emptyPStage (Fin 3) 2).Good mv mp eps ∧
    (0 : Fin 2) ∉ (PhaseTPS.emptyPStage (Fin 3) 2).served ∧
    (0 : Fin 3) ∈ (PhaseTPS.emptyPStage (Fin 3) 2).pool ∧
    2 * GeneralTPS.thr mv mp 0 < mp 0 ∧
    ¬ PhaseTPS.PureGood mv mp (PhaseTPS.emptyPStage (Fin 3) 2).served 0 ∧
    (∀ F : Finset (Fin 3), F ⊆ (PhaseTPS.emptyPStage (Fin 3) 2).pool →
      (∀ x ∈ F, PhaseTPS.PureGood mv mp (PhaseTPS.emptyPStage (Fin 3) 2).served x) →
      (PhaseTPS.emptyPStage (Fin 3) 2).bank + ∑ x ∈ F, mp x
        < CfgTPS.Qc mv mp ((PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps) 0
            (∅ : Finset (Fin 3))) := by sorry
