-- Prove2me | Theorems.Thm_FairSelling_GeneralTPS_total_nonneg
-- name    : FairSelling.GeneralTPS.total_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:13.983307+00:00
-- url     : https://prove2.me/theorems/2b7f1315-9f09-4ec7-88c9-615f97636021
-- title:
--   General TPS: total nonneg
-- statement:
--   The General TPS construction uses the total nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L257-L262
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L257-L262

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

theorem FairSelling.GeneralTPS.total_nonneg (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hp : ∀ g, 0 ≤ p g)
    {s : Stage G n} (hs : s.Good v p eps) : 0 ≤ s.total v p := by sorry
