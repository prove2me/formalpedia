-- Prove2me | Theorems.Thm_AlgebraicCurve_ell_le_degree_add_ellZero
-- name    : AlgebraicCurve.ell_le_degree_add_ellZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/ad62287e-6d19-5b7f-8ae7-4545166706b0
-- title:
--   Riemann's inequality: ℓ(D)≤deg D+ℓ(0)
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra satisfying `IsCurveOver K F`: every nonzero $f \in F$ admits a divisor $D$ with $D v = \operatorname{ord}_v f$ at every place $v$ and $\deg D = 0$; each place has residue field finite over $K$; and $\Omega_{F/K}$ is free of rank $1$ over $F$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring, and a divisor is a finitely supported function from places to $\mathbb{Z}$. Let $D$ be a divisor that is effective, i.e. $0 \le D$ pointwise, and assume that the Riemann–Roch space of the zero divisor, namely the $K$-subspace $\{f \in F : v(f) \le 1 \text{ for all } v\}$ cut out by the adic valuations, is finite-dimensional over $K$. Writing $\ell(E)$ for the $K$-dimension of the space $\{f \in F : v(f) \le \exp(E v) \text{ for all } v\}$ and $\deg D = \sum_v D v \cdot \deg v$ for the degree weighted by the degrees of the places, the conclusion is the inequality of integers $\ell(D) \le \deg D + \ell(0)$.
--
--   This is Riemann's inequality, the elementary half of the Riemann–Roch theorem for a one-variable function field, in effective form. It is used in the project's bound on the dimension of spaces attached to divisors with prescribed pole orders, and in the analysis of orders of functions on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ell_le_degree_add_ellZero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem ell_le_degree_add_ellZero {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] {D : Divisor K F}
    (hD : 0 ≤ D) [FiniteDimensional K ↥(LSpace (0 : Divisor K F))] :
    (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) := by sorry
