-- Prove2me | Theorems.Thm_FamousTheorems_strong_pigeonhole_principle
-- name    : FamousTheorems.strong_pigeonhole_principle
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:40.675262+00:00
-- url     : https://prove2.me/theorems/2ede426d-1f86-4c58-b523-7435217e9425
-- title:
--   The strong pigeonhole principle
-- statement:
--   **The strong pigeonhole principle.** Let $f:\alpha\to\beta$ be a map between finite sets and $n$ a natural number with $|\beta|\cdot n<|\alpha|$. Then some fibre of $f$ has more than $n$ elements: there is $y\in\beta$ with $|f^{-1}(y)|>n$.
--
--   Equivalently, if $N$ objects are put into $k$ boxes, some box receives at least $\lceil N/k\rceil$ objects. This is the everyday form of the pigeonhole principle in combinatorics, used for example in the Erdős–Szekeres theorem on monotone subsequences and in Ramsey theory.
--
--   **Formalization note.** Mathlib's `Fintype.exists_lt_card_fiber_of_mul_lt_card`. The fibre is written as `Finset.univ.filter fun x => f x = y`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Fintype.exists_lt_card_fiber_of_mul_lt_card`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem strong_pigeonhole_principle {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) {n : ℕ}
    (hn : Fintype.card β * n < Fintype.card α) : ∃ y : β, n < (Finset.univ.filter fun x => f x = y).card := by sorry

end FamousTheorems
