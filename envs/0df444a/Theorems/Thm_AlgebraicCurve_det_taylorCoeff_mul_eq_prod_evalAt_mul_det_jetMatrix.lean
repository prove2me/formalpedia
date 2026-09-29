-- Prove2me | Theorems.Thm_AlgebraicCurve_det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix
-- name    : AlgebraicCurve.det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/e4482018-3400-58b4-a5b3-90d55f05fdd1
-- title:
--   Rescaling by regular multipliers multiplies the jet determinant
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, and let $M$ be a natural number. Let $P_0,\dots,P_{M-1}$ be places of $F$ over $K$ (valuation subrings of $F$ containing the image of $K$, proper, and principal ideal rings), and let $t : \mathrm{Fin}\,M \to F$, $e : \mathrm{Fin}\,M \to \mathbb{N}$. Assume $(P,t,e)$ is a confluent pattern, i.e. $t_i$ depends only on the place $P_i$, distinct indices with the same place carry distinct orders $e_i$, and $e_i < \#\{i' : P_{i'} = P_i\}$ for every $i$; assume each $P_i$ is rational in the sense that $K$ surjects onto its residue field, and that $\operatorname{ord}_{P_i}(t_i) = 1$, the order being the negative logarithm of the associated adic valuation. Let $u : \mathrm{Fin}\,M \to F$ with every $u_j$ lying in the valuation subring of every $P_i$, and let $c$ assign to each place of $F$ over $K$ an element of $F$, with $c(P_i)$ lying in the valuation subring of $P_i$ for each $i$. Then the determinant of the matrix with $(i,j)$ entry the $e_i$-th Taylor coefficient at $P_i$ along $t_i$ of $u_j\,c(P_i)$ equals $\bigl(\prod_i \operatorname{ev}_{P_i}(c(P_i))\bigr)$ times the determinant of the jet matrix of $u$ at the data $(P,t,e)$, where $\operatorname{ev}_{v}$ denotes the $K$-valued residue evaluation at $v$ and the jet matrix has $(i,j)$ entry the $e_i$-th Taylor coefficient at $P_i$ along $t_i$ of $u_j$.
--
--   This is the multiplicativity of a confluent (jet) evaluation determinant under rescaling of the sections by multipliers depending only on the row's place: the determinant is scaled by the product of the values of the multipliers at the corresponding places. It is used in the construction of auxiliary functions for the height estimates of [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (hpat : IsConfluentPattern P t e) (hrat : ∀ i, (P i).IsRational) (hord : ∀ i, (P i).ord (t i) = 1)
    (u : Fin M → F) (hu : ∀ i j, u j ∈ (P i).toValuationSubring)
    (c : Place K F → F) (hc : ∀ i, c (P i) ∈ (P i).toValuationSubring) :
    (Matrix.of fun i j => (P i).taylorCoeff (t i) (e i) (u j * c (P i))).det
      = (∏ i, (P i).evalAt (c (P i))) * (jetMatrix P t e u).det := by sorry
