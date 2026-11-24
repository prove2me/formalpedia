-- Prove2me | Theorems.Thm_FairSelling_GeneralTPS_total_le_bound
-- name    : FairSelling.GeneralTPS.total_le_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:08.206256+00:00
-- url     : https://prove2.me/theorems/b6c9e4e0-809f-4ce1-941e-e033dbbfb5b0
-- title:
--   General TPS: total le bound
-- statement:
--   The General TPS construction uses the total le bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L238-L255
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L238-L255

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

theorem FairSelling.GeneralTPS.total_le_bound (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hp : ∀ g, 0 ≤ p g)
    {s : Stage G n} (hs : s.Good v p eps) :
    s.total v p ≤ totalBound v p := by sorry
