-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_eq_zero_iff
-- name    : DiscreteConvex.MixedMatrices.matrixSubRank_eq_zero_iff
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:34:16.749695+00:00
-- url     : https://prove2.me/theorems/c3a0d7eb-9d23-4c52-9cc1-6365f413a63a
-- title:
--   A submatrix has rank zero iff it vanishes
-- statement:
--   Let $R,C$ be finite index sets and $M$ an $R\times C$ matrix over a field, with $M[I,J]$ the submatrix with rows in $I\subseteq R$ and columns in $J\subseteq C$. For index sets $I,J$,
--
--   $$\operatorname{rank}M[I,J]=0\iff M_{ij}=0\ \text{ for all } i\in I,\ j\in J .$$
--
--   **Formalization Note.** `MatrixSubRank M I J` is the platform definition of $\operatorname{rank}M[I,J]$.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 12 (mixed matrices); elementary lemma used in formalising Theorem 12.8 (p. 358); not stated in the book

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

namespace DiscreteConvex.MixedMatrices

theorem matrixSubRank_eq_zero_iff {R C 𝔽 : Type*} [Fintype R] [Fintype C] [Field 𝔽]
    (M : Matrix R C 𝔽) (I : Finset R) (J : Finset C) :
    MatrixSubRank M I J = 0 ↔ ∀ i ∈ I, ∀ j ∈ J, M i j = 0 := by sorry

end DiscreteConvex.MixedMatrices
