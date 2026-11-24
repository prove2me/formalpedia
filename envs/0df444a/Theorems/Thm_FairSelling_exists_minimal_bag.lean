-- Prove2me | Theorems.Thm_FairSelling_exists_minimal_bag
-- name    : FairSelling.exists_minimal_bag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:54.484101+00:00
-- url     : https://prove2.me/theorems/12766d51-4a5b-4e14-8f9e-26e2faf5dc90
-- title:
--   Fair Selling: exists minimal bag
-- statement:
--   Bag filling: if every remaining good is worth less than its threshold to every active agent,
--   and some active agent can be satisfied by all of the goods plus the banked cash, then there is a
--   *nonempty* bundle `B` and an active agent `j` that reaches its threshold on `B` plus the cash,
--   while every active agent values `B` plus the cash at less than twice its own threshold.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L182-L228
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L182-L228

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

theorem FairSelling.exists_minimal_bag (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    (T : Finset (Fin n)) (R : Finset G) (D : ℝ)
    (hsmall : ∀ i ∈ T, ∀ g ∈ R, vbar (v i) p g < τ i)
    (hD : ∀ i ∈ T, D < τ i)
    (j₀ : Fin n) (hj₀ : j₀ ∈ T) (hfull : τ j₀ ≤ vbarSum (v j₀) p R + D) :
    ∃ (B : Finset G) (j : Fin n), B ⊆ R ∧ j ∈ T ∧
      τ j ≤ vbarSum (v j) p B + D ∧
      ∀ i ∈ T, vbarSum (v i) p B + D < 2 * τ i := by sorry
