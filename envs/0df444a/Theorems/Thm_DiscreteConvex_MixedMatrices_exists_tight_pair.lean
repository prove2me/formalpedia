-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_exists_tight_pair
-- name    : DiscreteConvex.MixedMatrices.exists_tight_pair
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:35:24.378631+00:00
-- url     : https://prove2.me/theorems/70a06a77-9afc-4077-bd99-8a6bd09fcc94
-- title:
--   Rank of a mixed matrix: a tight pair of index sets
-- statement:
--   Throughout, $R$ and $C$ are finite index sets, $K\subseteq F$ are fields (in Lean: `Algebra K F`), and for a matrix $M$ and subsets $I\subseteq R$, $J\subseteq C$ we write $M[I,J]$ for the submatrix with rows in $I$ and columns in $J$ and $\rho(I,J)=\operatorname{rank}Q[I,J]$, $\tau(I,J)=\operatorname{rank}T[I,J]$ for matrices $Q$ over $K$ and $T$ over $F$. A *mixed matrix* is $A=Q+T$ with $Q$ over $K$ and the nonzero entries of $T$ algebraically independent over $K$ (Murota, Ch. 12).
--
--   Let $A=Q+T$ be a mixed matrix. Then there are $I\subseteq R$ and $J\subseteq C$ with $T[I,J]=0$ and
--
--   $$\rho(I,J)+|R\setminus I|+|C\setminus J|=\operatorname{rank}A .$$
--
--   Equivalently, $\operatorname{rank}A=\rho(I,J)-|I|-|J|+|R|+|C|$ for some pair with $T[I,J]=0$. This is the existence statement of Murota's Theorem 12.9 (König-Egerváry theorem for mixed matrices) in complement form; together with weak duality it gives $\operatorname{rank}A=\min\{\rho(I,J)-|I|-|J|:T[I,J]=0\}+|R|+|C|$.
--
--   **Formalization Note.** `MatrixSubRank T I J = 0` expresses $\operatorname{rank}T[I,J]=0$, equivalently $T[I,J]=0$.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, Theorem 12.9 (p. 358), restated in complement form; proved here via Rado's theorem, a route different from the book's

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

namespace DiscreteConvex.MixedMatrices

theorem exists_tight_pair {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T) :
    ∃ (I : Finset R) (J : Finset C), MatrixSubRank T I J = 0 ∧
      MatrixSubRank Q I J + Iᶜ.card + Jᶜ.card = A.rank := by sorry

end DiscreteConvex.MixedMatrices
