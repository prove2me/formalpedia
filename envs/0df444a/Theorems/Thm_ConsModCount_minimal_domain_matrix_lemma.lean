-- Prove2me | Theorems.Thm_ConsModCount_minimal_domain_matrix_lemma
-- name    : ConsModCount.minimal_domain_matrix_lemma
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:25.738019+00:00
-- url     : https://prove2.me/theorems/edca89ec-56ca-4ffc-83d4-f682b1cc39be
-- title:
--   Lemma (Minimal-domain matrix lemma) — two diagonal and one antidiagonal summand
-- statement:
--   Let $M_1,\dots,M_k$ be nonzero nonnegative real $2\times2$ matrices with $k\ge3$. Suppose that every subset sum $\sum_{i\in S}M_i$ has rectangular support, every proper subset sum is block-rank-one, and the full sum $\sum_{i=1}^kM_i$ is not block-rank-one. Then $k=3$, and after possibly exchanging the two rows and/or the two columns of all summands and reordering the summands, $M_1$ and $M_2$ have exactly the positive diagonal support and $M_3$ has exactly the positive antidiagonal support.
--
--   The lemma identifies the three-state pattern in a domain-minimal obstruction.
--
--   Differences from the source:
--   - encoding: matrices M_1, …, M_k and the reordering of the summands → functions Fin 2 → Fin 2 → ℝ indexed by Fin k, and a bijection Fin 3 ≃ Fin k; reason: the Lean form of an indexed family
--   - encoding: exchanging rows or columns → a permutation of the two rows and a permutation of the two columns (each identity or swap), applied to every summand; reason: the Lean form of the exchange
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §11, Lemma (Minimal-domain matrix lemma), p.17 (PDF p.18)

import Definitions.Def_ConsModCount_Balance

set_option autoImplicit false

namespace ConsModCount

/-- **Lemma (Minimal-domain matrix lemma)** (Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §11, p.17, PDF p.18). Let `M₁, …, M_k` be nonzero
nonnegative real `2 × 2` matrices, with `k ≥ 3`. Suppose that every subset sum has rectangular
support, every proper subset sum is block-rank-one, and the full sum is not block-rank-one. Then
`k = 3`. Moreover, after possibly exchanging rows or columns and reordering the summands, `M₁` and
`M₂` have exactly the positive diagonal support and `M₃` has exactly the positive antidiagonal
support.

**Formalization Note.** Matrices are functions `Fin 2 → Fin 2 → ℝ`; subset sums range over all
`S ⊆ {1, …, k}` (the empty sum is the zero matrix). The reordering is `π : Fin 3 ≃ Fin k`; the
exchanges are permutations `ρ` of the rows and `κ` of the columns (each the identity or the swap),
applied to every summand. -/
theorem minimal_domain_matrix_lemma {k : ℕ} (M : Fin k → Fin 2 → Fin 2 → ℝ)
    (hnn : ∀ i a b, 0 ≤ M i a b) (hnz : ∀ i, M i ≠ 0) (hk : 3 ≤ k)
    (hrect : ∀ S : Finset (Fin k), RectangularSupport (fun a b => ∑ i ∈ S, M i a b))
    (hproper : ∀ S : Finset (Fin k), S ≠ Finset.univ →
      BlockRankOne (fun a b => ∑ i ∈ S, M i a b))
    (hfull : ¬ BlockRankOne (fun a b => ∑ i, M i a b)) :
    k = 3 ∧ ∃ (π : Fin 3 ≃ Fin k) (ρ κ : Equiv.Perm (Fin 2)),
      (∀ j : Fin 3, j ≠ 2 →
        0 < M (π j) (ρ 0) (κ 0) ∧ 0 < M (π j) (ρ 1) (κ 1) ∧
        M (π j) (ρ 0) (κ 1) = 0 ∧ M (π j) (ρ 1) (κ 0) = 0) ∧
      (0 < M (π 2) (ρ 0) (κ 1) ∧ 0 < M (π 2) (ρ 1) (κ 0) ∧
        M (π 2) (ρ 0) (κ 0) = 0 ∧ M (π 2) (ρ 1) (κ 1) = 0) := by sorry

end ConsModCount
