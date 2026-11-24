-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_lt_Qc_erase
-- name    : FairSelling.CfgTPS.lt_Qc_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:58:26.233799+00:00
-- url     : https://prove2.me/theorems/3ae0bc57-7a05-42e3-883d-1227f4434acd
-- title:
--   Cfg TPS: lt Qc erase
-- statement:
--   **Footprint minimality.**  Removing any single good from the footprint of the chosen package
--   leaves something that the free bank can no longer pay for.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L228-L253
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L228-L253

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
variable {w p req k0 D}
omit [Fintype G]

theorem FairSelling.CfgTPS.lt_Qc_erase {P S S₀ : Finset G} (hp : ∀ g, 0 ≤ p g) (hUP : S ∪ S₀ ⊆ P)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card)
    {g : G} (hg : g ∈ S ∪ S₀) : D < Qc w p req k0 ((S ∪ S₀) \ {g}) := by sorry
