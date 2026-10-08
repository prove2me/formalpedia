-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_mixed_matrix_rank_max_formula
-- name    : DiscreteConvex.MixedMatrices.mixed_matrix_rank_max_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T06:47:58.637443+00:00
-- url     : https://prove2.me/theorems/7cac430a-7b84-4dfd-8fdb-d514718fdde4
-- title:
--   Theorem 12.7 -- the rank of a mixed matrix, as a max-formula
-- statement:
--   **Theorem 12.7** (p.357, Eq. (12.9)). For a mixed matrix $A = Q + T$,
--   $$\operatorname{rank} A = \max\{\operatorname{rank} Q[I,J] + \operatorname{rank} T[R\setminus I, C\setminus J] \mid I \subseteq R,\ J \subseteq C\}.$$
--
--   A direct consequence of Proposition 12.6 applied to every submatrix of $A$. The maximization ranges over as many as $2^{|R|+|C|}$ pairs, too many for exhaustive search — Theorem 12.8 rewrites it as a minimization efficient algorithms can solve.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.357, Theorem 12.7.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.357, Theorem 12.7

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

namespace DiscreteConvex.MixedMatrices

/-- Theorem 12.7 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.357), Eq. (12.9). For a mixed
matrix `A = Q + T`, `rank A = max{rank Q[I,J] + rank T[R\I,C\J] | I ⊆ R, J ⊆ C}`. -/
theorem mixed_matrix_rank_max_formula {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T) :
    A.rank = (Finset.univ : Finset (Finset R)).sup (fun I =>
      (Finset.univ : Finset (Finset C)).sup (fun J =>
        MatrixSubRank Q I J + MatrixSubRank T Iᶜ Jᶜ)) := by sorry

end DiscreteConvex.MixedMatrices
