-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_truncBundle_add_le_two
-- name    : FairSelling.CfgTPS.truncBundle_add_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:53.108011+00:00
-- url     : https://prove2.me/theorems/bd0dcb2e-2f96-46ea-863d-f4152ed0b51f
-- title:
--   Cfg TPS: trunc Bundle add le two
-- statement:
--   **The cost of a footprint of at least two goods.**  Footprint minimality forces every good of
--   the footprint, and the footprint minus any good, to be worth less than `req j − D` to the agent
--   `j`, so the whole footprint is worth less than `2·(req j − D)`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L295-L327
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L295-L327

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

theorem FairSelling.CfgTPS.truncBundle_add_le_two {P S S₀ : Finset G} (t : Fin n → ℝ) (j : Fin n)
    (hp : ∀ g, 0 ≤ p g) (hD : 0 ≤ D) (hUP : S ∪ S₀ ⊆ P)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card)
    (hcard : 2 ≤ (S ∪ S₀).card) :
    truncBundle (w j) p (t j) (S ∪ S₀) + D ≤ 2 * req j := by sorry
