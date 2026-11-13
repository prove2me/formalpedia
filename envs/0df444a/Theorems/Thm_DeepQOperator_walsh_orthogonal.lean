-- Prove2me | Theorems.Thm_DeepQOperator_walsh_orthogonal
-- name    : DeepQOperator.walsh_orthogonal
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:01.100554+00:00
-- url     : https://prove2.me/theorems/9bae2d2b-beb9-4e9e-ac34-e52c224e15f4
-- title:
--   (54): Walsh words are orthogonal
-- statement:
--   Let $n=2^r$ and $c_i(v)=(-1)^{i\cdot v}$ for $v\in\{0,1\}^r$. For indices $i\ne j$ below $2^r$,
--   $$c_i^{\mathsf T}c_j=0,\qquad c_i^{\mathsf T}c_i=n,\qquad \|c_i-c_j\|_1=n.\tag{54}$$
--   The exponent is computed over the binary field and the inner products and norms over the reals.
--
--   Orthogonality of the Walsh rows is what bounds the squared Walsh scores (43) and separates the address boxes of the lower-bound prior.
--
--   **Formalization Note** Indices are natural numbers below $2^r$, read through their $r$-bit binary expansions; addresses are `Fin (2^r)`.
--
--   Differences from the source:
--   - generalization: Walsh words c_i with i ∈ {0, …, m − 1} → every pair of indices i ≠ j below 2^r, and c_iᵀc_i = n for every index; reason: m ≤ 2^r, so the paper's indices are among them
--   - encoding: v ∈ {0,1}^r → v : Fin (2^r) through its binary expansion; reason: bijection; same sums
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix G.1, eq. (54), p.28 (PDF p.31)

import Mathlib
import Definitions.Def_DeepQOperator_Family

open Finset

namespace DeepQOperator

/-- **(54), Walsh geometry** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix G.1, p.28, PDF p.31).

Write `V = {0,1}^r`, `n = 2^r`, `c_i(v) = (-1)^{i·v}`. For distinct `i, j`: `c_iᵀc_j = 0`,
`c_iᵀc_i = n` and `∥c_i - c_j∥₁ = n` (54). Subtraction in the exponent is over the binary field; inner
products and norms are over the reals.

**Formalization Note.** Walsh words are indexed by natural numbers `i, j < 2^r` (binary expansions of
length `r`) and addresses `v : Fin (2^r)`; `c_iᵀc_i = n` holds for every `i`.
-/
theorem walsh_orthogonal :
    (∀ r i j : ℕ, i < 2 ^ r → j < 2 ^ r → i ≠ j →
      ∑ v : Fin (2 ^ r), walsh r i v * walsh r j v = 0) ∧
    (∀ r i : ℕ, ∑ v : Fin (2 ^ r), walsh r i v * walsh r i v = (2 ^ r : ℝ)) ∧
    (∀ r i j : ℕ, i < 2 ^ r → j < 2 ^ r → i ≠ j →
      ∑ v : Fin (2 ^ r), |walsh r i v - walsh r j v| = (2 ^ r : ℝ)) := by sorry

end DeepQOperator
