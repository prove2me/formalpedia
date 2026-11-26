-- Prove2me | Theorems.Thm_Erdos287_hall_orientation_combines_local_layer_patterns
-- name    : Erdos287.hall_orientation_combines_local_layer_patterns
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:46:26.061752+00:00
-- url     : https://prove2.me/theorems/ce5bf167-2bef-5f25-bf26-cadd4aecb842
-- title:
--   Combining exact local layer patterns by an edge-to-layer assignment
-- statement:
--   Give each layer in a finite set a nonempty family of allowed retained-position patterns. Each edge joins two layers and names one position in each. Suppose each endpoint position can individually be retained by an allowed pattern of its own layer. If every subset of edges has at least as many incident layers as edges, then one can choose an allowed pattern in each layer with a retained endpoint on every edge.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.hall_orientation_combines_local_layer_patterns (P E : Finset ℕ) (left right posL posR : ℕ → ℕ)
    (F : ℕ → Finset (Finset ℕ))
    (hP : ∀ p ∈ P, (F p).Nonempty)
    (hE : ∀ e ∈ E, left e ∈ P ∧ right e ∈ P)
    (hL : ∀ e ∈ E, ∃ T ∈ F (left e), posL e ∈ T)
    (hR : ∀ e ∈ E, ∃ T ∈ F (right e), posR e ∈ T)
    (hHall : ∀ S ⊆ E, S.card ≤ ((S.image left) ∪ S.image right).card) :
    ∃ C : ℕ → Finset ℕ, (∀ p ∈ P, C p ∈ F p) ∧
      ∀ e ∈ E, posL e ∈ C (left e) ∨ posR e ∈ C (right e) := by sorry
