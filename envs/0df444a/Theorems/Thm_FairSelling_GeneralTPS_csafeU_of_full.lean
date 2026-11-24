-- Prove2me | Theorems.Thm_FairSelling_GeneralTPS_csafeU_of_full
-- name    : FairSelling.GeneralTPS.csafeU_of_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:13.963545+00:00
-- url     : https://prove2.me/theorems/16378746-5c31-423e-95bd-a2cb03e0da2c
-- title:
--   General TPS: csafe U of full
-- statement:
--   The General TPS construction uses the csafe U of full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L266-L277
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L266-L277

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

theorem FairSelling.GeneralTPS.csafeU_of_full (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) {s : Stage G n}
    (hs : s.Good v p eps) (hfull : s.served = Finset.univ) (i j : Fin n) :
    CSafeU v p eps s.bundle s.cash i j := by sorry
