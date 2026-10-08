-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_le_gammaFun
-- name    : DiscreteConvex.MixedMatrices.matrixSubRank_le_gammaFun
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:34:49.0363+00:00
-- url     : https://prove2.me/theorems/a858f871-09a0-425a-b1ee-1ddce1154a95
-- title:
--   The rank of a submatrix is at most its number of nonzero rows
-- statement:
--   Let $R,C$ be finite index sets and $T$ an $R\times C$ matrix over a field $F$, with $T[I,J]$ the submatrix with rows in $I\subseteq R$ and columns in $J\subseteq C$. For index sets $I,J$,
--
--   $$\tau(I,J)=\operatorname{rank}T[I,J]\le\gamma(I,J),$$
--
--   where $\gamma(I,J)$ is the number of nonzero rows of $T[I,J]$.
--
--   **Formalization Note.** `MatrixSubRank` and `GammaFun` are the platform definitions of $\operatorname{rank}T[I,J]$ and $\gamma(I,J)$.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 12 (mixed matrices), p. 357 (the function gamma); elementary lemma used in formalising Theorem 12.8; not stated in the book

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank
import Definitions.Def_DiscreteConvex_MixedMatrices_GammaFun

namespace DiscreteConvex.MixedMatrices

theorem matrixSubRank_le_gammaFun {R C F : Type*} [Fintype R] [Fintype C] [Field F]
    (T : Matrix R C F) (I : Finset R) (J : Finset C) :
    MatrixSubRank T I J ≤ GammaFun T I J := by sorry

end DiscreteConvex.MixedMatrices
