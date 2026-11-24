-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_not_adm_keep_all
-- name    : FairSelling.CfgTPS.not_adm_keep_all
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:58:35.366379+00:00
-- url     : https://prove2.me/theorems/e540b113-b89c-447f-a4b3-e8816001049d
-- title:
--   Cfg TPS: not adm keep all
-- statement:
--   **The tie-break.**  If the chosen package sells anything, then keeping the whole footprint is
--   not admissible.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L258-L266
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L258-L266

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

theorem FairSelling.CfgTPS.not_adm_keep_all {P S S₀ : Finset G} (hUP : S ∪ S₀ ⊆ P)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card)
    (hS₀ : S₀.Nonempty) : ¬ Adm w p req k0 D (S ∪ S₀) ∅ := by sorry
