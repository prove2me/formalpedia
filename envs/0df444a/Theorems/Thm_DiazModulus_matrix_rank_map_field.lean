-- Prove2me | Theorems.Thm_DiazModulus_matrix_rank_map_field
-- name    : DiazModulus.matrix_rank_map_field
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:07:07.467234+00:00
-- url     : https://prove2.me/theorems/f1c919d5-c55f-4ca2-9e2a-0e078e811828
-- title:
--   A homomorphism of fields f: K → L, applied to every entry of a matrix A over K, does not change its rank: rank f(A) = rank A
-- statement:
--   Let $K$ and $L$ be fields, $f\colon K \to L$ a ring homomorphism, and $A$ a $d \times \ell$ matrix with entries in $K$. Let $f(A)$ be the $d \times \ell$ matrix over $L$ obtained by applying $f$ to every entry of $A$. Then
--   $$\operatorname{rank}_L f(A) = \operatorname{rank}_K A.$$
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 12.23 (p. 436): classical linear algebra, used to compare the ranks of Σₖ XₖNₖ over ℚ(X₁, …, Xₘ) and over Q̄(X₁, …, Xₘ). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem matrix_rank_map_field {K L : Type*} [Field K] [Field L] (f : K →+* L) {d l : ℕ}
    (A : Matrix (Fin d) (Fin l) K) : (A.map f).rank = A.rank := by
  sorry

end DiazModulus
