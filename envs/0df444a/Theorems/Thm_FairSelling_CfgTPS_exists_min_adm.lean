-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_exists_min_adm
-- name    : FairSelling.CfgTPS.exists_min_adm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:41.472812+00:00
-- url     : https://prove2.me/theorems/518210f4-3701-4f0e-b777-b78fa45f72be
-- title:
--   Cfg TPS: exists min adm
-- statement:
--   **The choice of package.**  Among the admissible packages whose footprint lies in the pool,
--   choose one minimizing the pair (size of the footprint, number of goods sold), lexicographically.
--   The pool itself is feasible by hypothesis, so there is something to choose from.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L193-L221
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L193-L221

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
open Classical

theorem FairSelling.CfgTPS.exists_min_adm (P : Finset G) (hp : ∀ g, 0 ≤ p g) (hfeasP : Feas w p req k0 D P ∅) :
    ∃ S S₀ : Finset G, S ∪ S₀ ⊆ P ∧ Disjoint S S₀ ∧ Adm w p req k0 D S S₀ ∧
      ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card
          ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card := by sorry
