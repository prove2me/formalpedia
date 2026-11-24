-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_cost_bound
-- name    : FairSelling.CfgTPS.cost_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:31:50.687944+00:00
-- url     : https://prove2.me/theorems/29254d02-d791-4c7d-b7a5-b9501389bbb3
-- title:
--   Cfg TPS: cost bound
-- statement:
--   **The cost of the chosen package.**  Whatever its shape, the package chosen by
--   `exists_min_adm` costs any agent `j` whose requirement is a threshold at most twice that
--   threshold — the bound the counting argument needs.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L333-L445
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L333-L445

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable {w : Fin n → G → ℝ} {p : G → ℝ} {req : Fin n → ℝ} {k0 : Fin n} {D : ℝ}
omit [Fintype G]

theorem FairSelling.CfgTPS.cost_bound {P S S₀ : Finset G} (t : Fin n → ℝ) (j : Fin n)
    (hp : ∀ g, 0 ≤ p g) (hD : 0 ≤ D)
    (hreq0 : ∀ m, 0 ≤ req m) (hreqt : req j ≤ t j) (htreq : t j ≤ 2 * req j)
    (hUP : S ∪ S₀ ⊆ P) (hdisj : Disjoint S S₀) (hadm : Adm w p req k0 D S S₀)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card) :
    truncBundle (w j) p (t j) S + Qc w p req k0 S
      + ∑ g ∈ S₀, ChargeTPS.saleLoss (w j) p (t j) g ≤ 2 * req j := by sorry
