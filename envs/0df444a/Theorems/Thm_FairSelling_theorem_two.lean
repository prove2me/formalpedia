-- Prove2me | Theorems.Thm_FairSelling_theorem_two
-- name    : FairSelling.theorem_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:55:05.951872+00:00
-- url     : https://prove2.me/theorems/14c63d30-a4f5-450b-afad-9aeb46a36e0d
-- title:
--   Fair Selling: theorem two
-- statement:
--   **Theorem 2.**  Every allocation instance has an `n/(2n−1)`-TPS allocation, and moreover it
--   has an allocation that is both `n/(2n−1)`-TPS and SEFX.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxTheorem2.lean#L79-L84
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxTheorem2.lean#L79-L84

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

theorem FairSelling.theorem_two (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) :
    (∃ o : Outcome G n, o.Valid p ∧
      ∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧
    (∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o) := by sorry
