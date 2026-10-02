-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_konig_egervary_mixed_matrix
-- name    : DiscreteConvex.MixedMatrices.konig_egervary_mixed_matrix
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T06:48:08.84132+00:00
-- url     : https://prove2.me/theorems/57127834-fa4f-4b6b-95cc-23022065db8b
-- title:
--   Theorem 12.9 -- the König-Egerváry theorem for mixed matrices (goal)
-- statement:
--   **Theorem 12.9** (p.358), the goal theorem of this mission: the König-Egerváry theorem for mixed matrices. For a mixed matrix $A = Q + T$, there exist $I \subseteq R$ and $J \subseteq C$ such that
--
--   1. $|I| + |J| - \operatorname{rank} Q[I,J] = |R| + |C| - \operatorname{rank} A$, and
--   2. $\operatorname{rank} T[I,J] = 0$.
--
--   This is an immediate corollary of Theorem 12.8's third min-formula (take $(I,J)$ attaining the minimum), but it is the chapter's capstone precisely because of what it says on its own: it produces, for *any* mixed matrix, a combinatorial certificate of its rank deficiency — a submatrix $T[I,J]$ that vanishes entirely, paired with a numeric rank computation on the complementary $Q$-part — generalizing the classical König-Egerváry theorem (about 0-1 matrices, equivalently maximum bipartite matchings) to matrices mixing exact and generic entries.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.358, Theorem 12.9.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.358, Theorem 12.9

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

namespace DiscreteConvex.MixedMatrices

/-- Theorem 12.9 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.358), the goal theorem of this
mission: the König-Egerváry theorem for mixed matrices. For a mixed matrix `A = Q + T`, there
exist `I ⊆ R` and `J ⊆ C` such that (i) `|I| + |J| − rank Q[I,J] = |R| + |C| − rank A`, and
(ii) `rank T[I,J] = 0`. -/
theorem konig_egervary_mixed_matrix {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T) :
    ∃ I : Finset R, ∃ J : Finset C,
      ((I.card : ℤ) + J.card - MatrixSubRank Q I J = Fintype.card R + Fintype.card C - A.rank) ∧
      MatrixSubRank T I J = 0 := by sorry

end DiscreteConvex.MixedMatrices
