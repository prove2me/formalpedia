-- Prove2me | Theorems.Thm_FairSelling_not_SEFXlit_relaxation_of_EF
-- name    : FairSelling.not_SEFXlit_relaxation_of_EF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:17:37.3396+00:00
-- url     : https://prove2.me/theorems/fef81ab9-2d6f-408e-9af1-b40e4fdabde7
-- title:
--   Fair Selling: not SEFXlit relaxation of EF
-- statement:
--   **The literal reading of Definition 4.2 is not a relaxation of envy-freeness** either.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L124-L129
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean#L124-L129

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
set_option autoImplicit true
open scoped BigOperators
open FairSelling

theorem FairSelling.not_SEFXlit_relaxation_of_EF :
    ¬ ∀ (v : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) (o : Outcome (Fin 2) 2),
        (∀ i g, 0 ≤ v i g) → (∀ g, 0 ≤ p g) → o.Valid p → EF v p o → SEFXlit v p o := by sorry
