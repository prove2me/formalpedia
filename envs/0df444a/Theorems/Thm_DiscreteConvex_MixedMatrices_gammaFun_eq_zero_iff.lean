-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_gammaFun_eq_zero_iff
-- name    : DiscreteConvex.MixedMatrices.gammaFun_eq_zero_iff
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:34:41.949573+00:00
-- url     : https://prove2.me/theorems/ec65c2a5-9404-4f75-a2ad-82ec1f0e1a59
-- title:
--   The row count gamma vanishes iff the submatrix vanishes
-- statement:
--   Let $R,C$ be finite index sets, $T$ an $R\times C$ matrix, $T[I,J]$ the submatrix with rows in $I\subseteq R$ and columns in $J\subseteq C$, and $\gamma(I,J)$ the number of rows $i\in I$ with $T_{ij}\neq0$ for some $j\in J$ (the number of nonzero rows of $T[I,J]$). Then
--
--   $$\gamma(I,J)=0\iff T_{ij}=0\ \text{ for all } i\in I,\ j\in J .$$
--
--   **Formalization Note.** `GammaFun T I J` is the platform definition of $\gamma(I,J)$.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 12 (mixed matrices), p. 357 (the function gamma); elementary lemma used in formalising Theorem 12.8; not stated in the book

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_GammaFun

namespace DiscreteConvex.MixedMatrices

theorem gammaFun_eq_zero_iff {R C F : Type*} [Zero F] (T : Matrix R C F) (I : Finset R)
    (J : Finset C) :
    GammaFun T I J = 0 ↔ ∀ i ∈ I, ∀ j ∈ J, T i j = 0 := by sorry

end DiscreteConvex.MixedMatrices
