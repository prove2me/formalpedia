-- Prove2me | Theorems.Thm_FairSelling_servable_empty
-- name    : FairSelling.servable_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:25.076269+00:00
-- url     : https://prove2.me/theorems/0b29c018-f405-4e22-a4a9-57289f0f4f96
-- title:
--   Fair Selling: servable empty
-- statement:
--   When no agent is active there is nothing to do.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L42-L47
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L42-L47

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsLemma9
import Definitions.Def_RequestProject_TwoThirds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.servable_empty (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ) (R : Finset G) {D : ℝ}
    (hD : 0 ≤ D) : Servable v p τ (∅ : Finset (Fin n)) R D := by sorry
