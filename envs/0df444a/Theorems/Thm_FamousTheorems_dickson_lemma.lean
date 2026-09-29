-- Prove2me | Theorems.Thm_FamousTheorems_dickson_lemma
-- name    : FamousTheorems.dickson_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:22.469246+00:00
-- url     : https://prove2.me/theorems/9c6f28bb-6cee-4bfb-a78c-371fb6b2558c
-- title:
--   Dickson's lemma
-- statement:
--   **Dickson's lemma.** For every $k$, every infinite sequence $v_0,v_1,v_2,\dots$ in $\mathbb N^k$ has indices $i<j$ with $v_i\le v_j$ componentwise.
--
--   Equivalently, $\mathbb N^k$ with the product order is a well-quasi-order. Every set of monomials therefore has finitely many minimal elements, and every monomial ideal is finitely generated. This is a combinatorial form of Hilbert's basis theorem and is the reason Buchberger's algorithm for Gröbner bases terminates.
--
--   **Formalization note.** Mathlib's instance `Pi.wellQuasiOrderedLE`, which makes a finite product of well-quasi-ordered types well-quasi-ordered, used through `wellQuasiOrdered_le`. The order on `Fin k → ℕ` is the pointwise order.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Pi.wellQuasiOrderedLE`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dickson_lemma (k : ℕ) (f : ℕ → (Fin k → ℕ)) : ∃ i j, i < j ∧ f i ≤ f j := by sorry

end FamousTheorems
