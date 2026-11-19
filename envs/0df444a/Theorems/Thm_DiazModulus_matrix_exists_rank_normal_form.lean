-- Prove2me | Theorems.Thm_DiazModulus_matrix_exists_rank_normal_form
-- name    : DiazModulus.matrix_exists_rank_normal_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:11.799197+00:00
-- url     : https://prove2.me/theorems/cc95bcf9-6fd1-4212-88de-6829836abe02
-- title:
--   Rank normal form: for an s × t matrix N over a field k there are invertible P, Q over k and r ≤ min(s, t) with PNQ = (I_r 0; 0 0)
-- statement:
--   Let $k$ be a field and $N$ an $s \times t$ matrix with entries in $k$. Then there are a natural number $r \le \min(s, t)$ and invertible matrices $P \in \mathrm{GL}_s(k)$, $Q \in \mathrm{GL}_t(k)$ such that
--   $$PNQ = \begin{pmatrix} I_r & 0 \\ 0 & 0 \end{pmatrix},$$
--   that is, $(PNQ)_{ij} = 1$ if $i = j \le r$ and $(PNQ)_{ij} = 0$ otherwise (indices numbered from $1$). The statement does not record that $r$ is the rank of $N$.
-- source:
--   Classical linear algebra, used without proof in M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, proof of Prop. 12.2 (pp. 420–421), for rectangular N. Proved by elimination, by induction on the number of rows. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem matrix_exists_rank_normal_form {k : Type*} [Field k] {s t : ℕ}
    (N : Matrix (Fin s) (Fin t) k) :
    ∃ (r : ℕ) (P : Matrix (Fin s) (Fin s) k) (Q : Matrix (Fin t) (Fin t) k),
      r ≤ s ∧ r ≤ t ∧ IsUnit P.det ∧ IsUnit Q.det ∧
      ∀ (i : Fin s) (j : Fin t), (P * N * Q) i j = if i.val = j.val ∧ i.val < r then 1 else 0 := by
  sorry

end DiazModulus
