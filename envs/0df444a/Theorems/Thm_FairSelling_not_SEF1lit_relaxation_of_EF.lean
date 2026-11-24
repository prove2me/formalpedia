-- Prove2me | Theorems.Thm_FairSelling_not_SEF1lit_relaxation_of_EF
-- name    : FairSelling.not_SEF1lit_relaxation_of_EF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:17:41.851911+00:00
-- url     : https://prove2.me/theorems/97f08157-d6f8-4619-8e65-2e9639ad4a8e
-- title:
--   Fair Selling: not SEF1lit relaxation of EF
-- statement:
--   **The literal reading of Definition 4.1 is not a relaxation of envy-freeness.**  There is an
--   instance with non-negative valuations and prices and a *full* envy-free allocation of it that does
--   not satisfy `SEF1lit`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L116-L121
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L116-L121

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
set_option autoImplicit true
open scoped BigOperators
open FairSelling

theorem FairSelling.not_SEF1lit_relaxation_of_EF :
    ¬ ∀ (v : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) (o : Outcome (Fin 2) 2),
        (∀ i g, 0 ≤ v i g) → (∀ g, 0 ≤ p g) → o.Valid p → EF v p o → SEF1lit v p o := by sorry
