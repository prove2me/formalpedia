-- Prove2me | Theorems.Thm_DiazModulus_matrix_rank_le_of_zero_block
-- name    : DiazModulus.matrix_rank_le_of_zero_block
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:30:41.265199+00:00
-- url     : https://prove2.me/theorems/ad13a283-f591-4a27-9411-be1ea715308c
-- title:
--   A matrix with a zero block: if a d × ℓ matrix N over a field has Nᵢⱼ = 0 for i ≤ d′ and j > ℓ′, where d′ ≤ d, then rank N + d′ ≤ d + ℓ′
-- statement:
--   Let $K$ be a field, $N = (N_{ij})$ a $d \times \ell$ matrix with entries in $K$, and $d' \le d$ and $\ell'$ natural numbers such that $N_{ij} = 0$ whenever $i \le d'$ and $j > \ell'$ (rows and columns are numbered from $1$). Then
--   $$\operatorname{rank} N + d' \le d + \ell'.$$
-- source:
--   Classical linear algebra; a step of the proofs of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 12.18 (p. 433) and Cor. 12.22 (p. 436). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem matrix_rank_le_of_zero_block {K : Type*} [Field K] {d l : ℕ} (N : Matrix (Fin d) (Fin l) K)
    (d' l' : ℕ) (hz : ∀ (i : Fin d) (j : Fin l), i.val < d' → l' ≤ j.val → N i j = 0) (hd' : d' ≤ d) :
    N.rank + d' ≤ d + l' := by
  sorry

end DiazModulus
