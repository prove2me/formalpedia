-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_mono
-- name    : DiscreteConvex.MixedMatrices.matrixSubRank_mono
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:34:40.34558+00:00
-- url     : https://prove2.me/theorems/79847788-a21c-4021-9c19-ad27f829b67b
-- title:
--   Rank of a submatrix is monotone in the index sets
-- statement:
--   Let $R,C$ be finite index sets and $M$ an $R\times C$ matrix over a field, with $M[I,J]$ the submatrix with rows in $I\subseteq R$ and columns in $J\subseteq C$. For index sets $I\subseteq I'$, $J\subseteq J'$,
--
--   $$\operatorname{rank}M[I,J]\le\operatorname{rank}M[I',J'] .$$
--
--   **Formalization Note.** `MatrixSubRank M I J` is the platform definition of $\operatorname{rank}M[I,J]$.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 12 (mixed matrices); elementary lemma used in formalising Theorem 12.8 (p. 358); not stated in the book

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

namespace DiscreteConvex.MixedMatrices

theorem matrixSubRank_mono {R C 𝔽 : Type*} [Fintype R] [Fintype C] [Field 𝔽]
    (M : Matrix R C 𝔽) {I I' : Finset R} {J J' : Finset C} (hI : I ⊆ I') (hJ : J ⊆ J') :
    MatrixSubRank M I J ≤ MatrixSubRank M I' J' := by sorry

end DiscreteConvex.MixedMatrices
