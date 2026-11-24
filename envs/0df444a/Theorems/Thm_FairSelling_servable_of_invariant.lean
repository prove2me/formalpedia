-- Prove2me | Theorems.Thm_FairSelling_servable_of_invariant
-- name    : FairSelling.servable_of_invariant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:53:02.561033+00:00
-- url     : https://prove2.me/theorems/5c00dd29-49a5-4f3d-92cf-9ed19a399c94
-- title:
--   Fair Selling: servable of invariant
-- statement:
--   **The engine of Algorithm 4.**  If, with `m` agents still active, every active agent values
--   the remaining goods (through its truncated contributions) plus the banked cash at least
--   `(2m−1)·τ i`, then all active agents can be served their thresholds.  The three cases of the
--   proof are the three loops of the manuscript's Algorithm 4.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L238-L360
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L238-L360

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
open Classical

theorem FairSelling.servable_of_invariant (v : Fin n → G → ℝ) (p : G → ℝ) (τ t : Fin n → ℝ) (hτ : ∀ i, 0 ≤ τ i) (ht : ∀ i, t i ≤ 2 * τ i) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → 0 ≤ D →
      (∀ i ∈ T, (2 * (m : ℝ) - 1) * τ i ≤ truncBundle (v i) p (t i) R + D) →
      Servable v p τ T R D := by sorry
