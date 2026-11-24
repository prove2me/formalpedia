-- Prove2me | Theorems.Thm_FairSelling_GeneralTPS_truncBundle_univ
-- name    : FairSelling.GeneralTPS.truncBundle_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:27:23.341019+00:00
-- url     : https://prove2.me/theorems/7596d553-c8e5-41fa-aa43-f48f86039d50
-- title:
--   General TPS: trunc Bundle univ
-- statement:
--   The General TPS construction uses the trunc Bundle univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L206-L213
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L206-L213

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.GeneralTPS.truncBundle_univ (w p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) :
    truncBundle w p (TPS n w p) Finset.univ = (n : ℝ) * TPS n w p := by sorry
