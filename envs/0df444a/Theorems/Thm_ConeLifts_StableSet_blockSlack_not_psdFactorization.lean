-- Prove2me | Theorems.Thm_ConeLifts_StableSet_blockSlack_not_psdFactorization
-- name    : ConeLifts.StableSet.blockSlack_not_psdFactorization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:20:11.367838+00:00
-- url     : https://prove2.me/theorems/a899b231-d8b6-4ead-ad37-3675b9b204a0
-- title:
--   Theorem 5.2, proof — the block matrix $S'$ with blocks $1, 0_n, *_n, I_n$ has no $\mathcal S^n_+$-factorization
-- statement:
--   Let $n \ge 0$ and let $s \in \mathbb R^n$ be arbitrary. Consider the $(n+1)\times(n+1)$ block matrix
--
--   $$
--   S' = \begin{pmatrix} 1 & 0_n \\ s & I_n \end{pmatrix},
--   $$
--
--   where $0_n$ is the $1\times n$ zero row, $s$ is an $n \times 1$ column and $I_n$ is the $n\times n$ identity. Then $S'$ has no $\mathcal S^n_+$-factorization: there are no $n\times n$ real symmetric positive semidefinite matrices $A_0,\dots,A_n$ (for the rows) and $B_0,\dots,B_n$ (for the columns) with $\mathrm{tr}(A_i B_j) = S'_{ij}$ for all $i, j$.
--
--   In the proof of Theorem 5.2, $S'$ is the submatrix of the slack matrix of $\mathrm{STAB}(G)$ with rows $0, e_1, \dots, e_n$ and columns a facet not through the origin followed by the $n$ facets $x_i \ge 0$. A factorization of a matrix restricts to a factorization of each of its submatrices, so this lemma rules out $\mathcal S^n_+$-factorizations of the whole slack matrix.
--
--   **Formalization Note** Rows and columns are indexed by `Fin 1 ⊕ Fin n` and $S'$ is `Matrix.fromBlocks 1 0 s 1`. The column $s$ (the paper's "unknown" $*_n$) is an arbitrary real vector: its entries are nonnegative in the application, but the statement does not need this. For $n = 0$ the statement says that the $1\times 1$ matrix $(1)$ has no factorization by $0\times 0$ matrices, which is true since their trace products are $0$.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 19, Theorem 5.2 (proof)

import Mathlib
import Definitions.Def_ConeLifts_StableSet_HasPSDFactorization

namespace ConeLifts.StableSet

/-- **Theorem 5.2, proof** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 19): the block matrix
`S′ = [[1, 0ₙ], [∗ₙ, Iₙ]]` has no `Sⁿ₊`-factorization, whatever the `n × 1` column `∗ₙ`.

Rows are indexed by `Fin 1 ⊕ Fin n` (the origin, then `e₁, …, eₙ`) and columns by
`Fin 1 ⊕ Fin n` (the facet not touching the origin, then the `n` nonnegativity facets); `0ₙ` is
the `1 × n` zero block and `Iₙ` the `n × n` identity. The column `∗ₙ = s` is arbitrary (the
paper calls it "some unknown n × 1 vector"; its entries are nonnegative in the application, but
the statement holds for every real `s`). -/
theorem blockSlack_not_psdFactorization {n : ℕ} (s : Fin n → ℝ) :
    ¬ HasPSDFactorization n
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin n) ℝ)
        (Matrix.of fun (i : Fin n) (_ : Fin 1) => s i) (1 : Matrix (Fin n) (Fin n) ℝ)) := by sorry

end ConeLifts.StableSet
