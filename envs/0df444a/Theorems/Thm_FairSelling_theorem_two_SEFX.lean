-- Prove2me | Theorems.Thm_FairSelling_theorem_two_SEFX
-- name    : FairSelling.theorem_two_SEFX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:30.563803+00:00
-- url     : https://prove2.me/theorems/866ec47e-59e1-4fb3-9ce7-2612b6423789
-- title:
--   Fair Selling: theorem two SEFX
-- statement:
--   **Theorem 2, second half.**  Every allocation instance admits a valid outcome that gives
--   every agent at least `n/(2n−1)` of its truncated proportional share and is SEFX.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxTheorem2.lean#L71-L75
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxTheorem2.lean#L71-L75

import Mathlib
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxPotImp
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxTheorem2
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.theorem_two_SEFX (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by sorry
