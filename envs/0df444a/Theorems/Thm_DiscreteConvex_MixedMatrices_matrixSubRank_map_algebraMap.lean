-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_map_algebraMap
-- name    : DiscreteConvex.MixedMatrices.matrixSubRank_map_algebraMap
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:34:08.760558+00:00
-- url     : https://prove2.me/theorems/f9d4169b-f974-4f6e-a193-646dc387e3c4
-- title:
--   Rank of a submatrix is invariant under field extension
-- statement:
--   Let $R,C$ be finite index sets and $K\subseteq F$ fields (in Lean: `Algebra K F`). For a matrix $Q$ over $K$ and $I\subseteq R$, $J\subseteq C$ write $Q[I,J]$ for the submatrix with rows in $I$ and columns in $J$. Then for all $I,J$,
--
--   $$\operatorname{rank}_F\bigl(Q[I,J]\bigr)=\operatorname{rank}_K\bigl(Q[I,J]\bigr),$$
--
--   that is, the rank of a matrix does not change when its entries are viewed in a larger field.
--
--   **Formalization Note.** `Q.map (algebraMap K F)` is $Q$ viewed over $F$; `MatrixSubRank` is the platform definition of the rank of a submatrix.
-- source:
--   Standard fact on matrices over fields (the rank does not change under extension of the field); used in formalising Murota, Discrete Convex Analysis, SIAM 2003, Theorems 12.7-12.8; not stated in the book

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

namespace DiscreteConvex.MixedMatrices

theorem matrixSubRank_map_algebraMap {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] (Q : Matrix R C K) (I : Finset R) (J : Finset C) :
    MatrixSubRank (Q.map (algebraMap K F)) I J = MatrixSubRank Q I J := by sorry

end DiscreteConvex.MixedMatrices
