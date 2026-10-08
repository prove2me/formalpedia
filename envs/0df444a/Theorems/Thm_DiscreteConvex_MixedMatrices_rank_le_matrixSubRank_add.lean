-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_rank_le_matrixSubRank_add
-- name    : DiscreteConvex.MixedMatrices.rank_le_matrixSubRank_add
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:35:15.2196+00:00
-- url     : https://prove2.me/theorems/32be9321-0e9f-4c20-8c4a-b05a2a19daa8
-- title:
--   Weak duality for the rank of a mixed matrix
-- statement:
--   Throughout, $R$ and $C$ are finite index sets, $K\subseteq F$ are fields (in Lean: `Algebra K F`), and for a matrix $M$ and subsets $I\subseteq R$, $J\subseteq C$ we write $M[I,J]$ for the submatrix with rows in $I$ and columns in $J$ and $\rho(I,J)=\operatorname{rank}Q[I,J]$, $\tau(I,J)=\operatorname{rank}T[I,J]$ for matrices $Q$ over $K$ and $T$ over $F$. A *mixed matrix* is $A=Q+T$ with $Q$ over $K$ and the nonzero entries of $T$ algebraically independent over $K$ (Murota, Ch. 12).
--
--   Let $K\subseteq F$ be fields and $A=Q+T$ entrywise, with $Q$ over $K$ and $T$ over $F$. Then for all $I\subseteq R$, $J\subseteq C$,
--
--   $$\operatorname{rank}A\le\rho(I,J)+\tau(I,J)+|R\setminus I|+|C\setminus J| .$$
--
--   This is the easy (weak duality) inequality behind the min-formulas for the rank of a mixed matrix. No independence of the entries of $T$ is needed.
--
--   **Formalization Note.** The hypothesis is only the entrywise decomposition `A i j = algebraMap K F (Q i j) + T i j`.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 12 (mixed matrices), Theorem 12.8 (p. 358): the inequality rank A <= the minima in Eqs. (12.10)-(12.12) (weak duality)

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

namespace DiscreteConvex.MixedMatrices

theorem rank_le_matrixSubRank_add {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F)
    (hA : ∀ i j, A i j = algebraMap K F (Q i j) + T i j) (I : Finset R) (J : Finset C) :
    A.rank ≤ MatrixSubRank Q I J + MatrixSubRank T I J + Iᶜ.card + Jᶜ.card := by sorry

end DiscreteConvex.MixedMatrices
