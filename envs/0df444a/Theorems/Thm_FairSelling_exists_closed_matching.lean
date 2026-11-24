-- Prove2me | Theorems.Thm_FairSelling_exists_closed_matching
-- name    : FairSelling.exists_closed_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:24.529271+00:00
-- url     : https://prove2.me/theorems/8487a149-6a76-49a4-81ae-b22c8f22fdd8
-- title:
--   Fair Selling: exists closed matching
-- statement:
--   **The matching step.**  Given a set `A` of agents, a set `B` of parts with at least as many
--   parts as agents, and an acceptability relation, there are a set `K ⊆ A` of agents and an
--   injective assignment `f` of parts of `B` to them such that
--
--   * every agent of `K` accepts the part assigned to it;
--   * no agent of `A \ K` accepts any part assigned to an agent of `K`;
--   * either every agent is matched (`K = A`), or there is a part of `B`, unassigned, that no agent
--     of `A \ K` accepts.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsMatching.lean#L66-L193
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsMatching.lean#L66-L193

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsMatching
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem FairSelling.exists_closed_matching [Nonempty β]
    (acc : α → β → Prop) [DecidableRel acc] :
    ∀ (m : ℕ) (A : Finset α) (B : Finset β), A.card = m → A.card ≤ B.card →
    ∃ (K : Finset α) (f : α → β), K ⊆ A ∧ Set.InjOn f K ∧
      (∀ k ∈ K, f k ∈ B) ∧ (∀ k ∈ K, acc k (f k)) ∧
      (∀ a ∈ A, a ∉ K → ∀ k ∈ K, ¬ acc a (f k)) ∧
      (K = A ∨ ∃ b ∈ B, b ∉ K.image f ∧ ∀ a ∈ A, a ∉ K → ¬ acc a b) := by sorry
