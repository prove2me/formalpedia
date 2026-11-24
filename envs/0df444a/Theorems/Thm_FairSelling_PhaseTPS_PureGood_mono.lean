-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PureGood_mono
-- name    : FairSelling.PhaseTPS.PureGood.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:51.679022+00:00
-- url     : https://prove2.me/theorems/ad84fbf1-0cda-4195-b71f-fcc5c93ee4e7
-- title:
--   Pure Good: mono
-- statement:
--   The Pure Good construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L64-L66
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L64-L66

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.PhaseTPS.PureGood.mono {v : Fin n → G → ℝ} {p : G → ℝ} {A B : Finset (Fin n)} (hAB : A ⊆ B)
    {g : G} (h : PureGood v p A g) : PureGood v p B g := by sorry
