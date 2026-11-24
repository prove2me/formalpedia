-- Prove2me | Theorems.Thm_FairSelling_le_MMSEP
-- name    : FairSelling.le_MMSEP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:37:21.598041+00:00
-- url     : https://prove2.me/theorems/455c030d-379a-4395-9dc6-66d68a8d6a9e
-- title:
--   Fair Selling: le MMSEP
-- statement:
--   A lower bound on the equal-proceeds MMS is certified by exhibiting a valid equal-proceeds
--   outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L80-L82
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L80-L82

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.le_MMSEP (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    {r : ℝ} (hr : r ∈ MMSEPset n v p) : r ≤ MMSEP n v p := by sorry
