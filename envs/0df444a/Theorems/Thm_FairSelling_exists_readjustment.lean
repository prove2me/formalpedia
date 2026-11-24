-- Prove2me | Theorems.Thm_FairSelling_exists_readjustment
-- name    : FairSelling.exists_readjustment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:07.503428+00:00
-- url     : https://prove2.me/theorems/cb94e8bf-45c3-4236-a398-b9be27396320
-- title:
--   Fair Selling: exists readjustment
-- statement:
--   **Lemma 6 (value readjustment).**  Every instance can be replaced by one with pointwise
--   smaller valuations, the same maximin shares, and in which every agent has an equi-valued MMS
--   partition.  Since the valuations only decrease, an allocation guaranteeing `ρ·MMS` in the
--   readjusted instance guarantees `ρ·MMS` in the original one.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean#L352-L359
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean#L352-L359

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.exists_readjustment (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ v' : Fin n → G → ℝ, (∀ i g, 0 ≤ v' i g) ∧ (∀ i g, v' i g ≤ v i g) ∧
      (∀ i, MMS n (v' i) p = MMS n (v i) p) ∧
      ∀ i, Nonempty (EquiMMS (v' i) p (MMS n (v' i) p) n) := by sorry
