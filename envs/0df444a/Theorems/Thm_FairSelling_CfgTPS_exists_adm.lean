-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_exists_adm
-- name    : FairSelling.CfgTPS.exists_adm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:41.541801+00:00
-- url     : https://prove2.me/theorems/f6432c8c-d698-4a01-b723-2939e5fe5e65
-- title:
--   Cfg TPS: exists adm
-- statement:
--   **Shrinking.**  Every feasible package can be turned into an admissible package with the same
--   footprint, by repeatedly selling a set of goods that some agent envies.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L122-L177
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L122-L177

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n) (D : ℝ)
omit [Fintype G]

theorem FairSelling.CfgTPS.exists_adm (hp : ∀ g, 0 ≤ p g) :
    ∀ (c : ℕ) (S S₀ : Finset G), S.card ≤ c → Disjoint S S₀ → Feas w p req k0 D S S₀ →
      ∃ T T₀ : Finset G, T ⊆ S ∧ S₀ ⊆ T₀ ∧ T ∪ T₀ = S ∪ S₀ ∧ Disjoint T T₀ ∧
        Adm w p req k0 D T T₀ := by sorry
