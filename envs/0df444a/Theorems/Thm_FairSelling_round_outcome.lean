-- Prove2me | Theorems.Thm_FairSelling_round_outcome
-- name    : FairSelling.round_outcome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:36.533235+00:00
-- url     : https://prove2.me/theorems/2e58218b-ddba-4b5a-87ff-3a00ea98e179
-- title:
--   Fair Selling: round outcome
-- statement:
--   **The matching phase of one round.**  Let `i` be an active agent holding a canonical
--   partition of the available resources into `|T|` parts (each acceptable to `i`).  Then there are a
--   set `Kset` of agents served in this round (containing `i`) and an injective assignment `part` of
--   parts to them such that every served agent finds its part acceptable, every still-active agent
--   finds *every* part handed out in the round unacceptable, and only `i` may receive the special
--   part.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L289-L379
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L289-L379

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]

theorem FairSelling.round_outcome (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ} {μ : ℝ} {i : Fin n} (hi : i ∈ T)
    {k : ℕ} [NeZero k] (hk : T.card = k)
    (C : Canonical (v i) p μ (τ i) k R D) :
    ∃ (Kset : Finset (Fin n)) (part : Fin n → Fin k),
      i ∈ Kset ∧ Kset ⊆ T ∧ Set.InjOn part Kset ∧
      (∀ a ∈ Kset, τ a ≤ vbarSum (v a) p (C.goods (part a)) + C.cash (part a)) ∧
      (∀ a ∈ T, a ∉ Kset → ∀ b ∈ Kset,
          vbarSum (v a) p (C.goods (part b)) + C.cash (part b) < τ a) ∧
      (∀ a ∈ Kset, a ≠ i → part a ≠ 0) ∧ (Kset = T ∨ part i ≠ 0) := by sorry
