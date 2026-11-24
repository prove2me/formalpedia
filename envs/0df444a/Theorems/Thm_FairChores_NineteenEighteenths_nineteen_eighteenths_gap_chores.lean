-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_nineteen_eighteenths_gap_chores
-- name    : FairChores.NineteenEighteenths.nineteen_eighteenths_gap_chores
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:23:12.955953+00:00
-- url     : https://prove2.me/theorems/dd292235-028f-4d2f-8763-0c7b03b2ffa2
-- title:
--   Nineteen Eighteenths: nineteen eighteenths gap chores
-- statement:
--   **The `19/18` gap for chores with outsourcing**, packaged: for every `ρ < 19/18` there is
--   an instance with `n = 3` agents and `m = 8` chores (non-negative additive costs, non-negative
--   outsourcing prices) in which no feasible outcome keeps every agent's cost at or below `ρ`
--   times her maximin share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L338-L346
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L338-L346

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores

theorem FairChores.NineteenEighteenths.nineteen_eighteenths_gap_chores {rho : ℝ} (hrho : rho < 19/18) :
    ∃ (c : Fin 3 → Fin 8 → ℝ) (p : Fin 8 → ℝ),
      (∀ i t, 0 ≤ c i t) ∧ (∀ t, 0 ≤ p t) ∧
      ∀ o : Outcome (Fin 8) 3, o.Valid p →
        ∃ i, rho * MMS 3 (c i) p < cost (c i) o i := by sorry
