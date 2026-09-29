-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_divisor_degree_eq_one_of_finite
-- name    : AlgebraicCurve.exists_divisor_degree_eq_one_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/fb121d26-41c6-573e-9e6f-19b101adc1d5
-- title:
--   F. K. Schmidt: existence of a degree-one divisor
-- statement:
--   Let $k$ be a finite field and $F$ a field equipped with a $k$-algebra structure, such that $F$ is a curve over $k$ in the sense of the project's class [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a finitely supported $\mathbb{Z}$-valued function $D$ on the places of $F/k$ whose value at each place $v$ is the order $v.\mathrm{ord}\,f$ and whose degree is $0$; for each place $v$ the residue field of $v$ is a finite-dimensional $k$-module; and the module of Kähler differentials $\Omega[F/k]$ is free of rank $1$ over $F$. Here a place is a valuation subring of $F$ containing the image of $k$, different from $F$ itself, and a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$, and its degree is the additive homomorphism $D \mapsto \sum_v D(v)\deg v$ weighting each coefficient by the degree of the corresponding place. Assume furthermore that $F$ is of essentially finite type over $k$, and that $k$ is the full constant field in the sense of [`AlgebraicCurve.ConstantsAreBase`](def/AlgebraicCurve_AdelicIndex.html#L45): the Riemann–Roch space $L(0)$ of the zero divisor coincides with the image of $k$ in $F$ under the $k$-linear structure map. Then there exists a divisor $D$ of $F/k$ with $\deg D = 1$.
--
--   This is F. K. Schmidt's theorem, that the degree map on divisors of a function field over a finite full constant field is surjective onto $\mathbb{Z}$. It underlies the rationality and normalisation statements for the zeta function of the curve, and is used for the $L$-polynomial results [`AlgebraicCurve.exists_LPolynomial_of_finite`](thm.html#AlgebraicCurve.exists_LPolynomial_of_finite) and [`AlgebraicCurve.LPolynomial_eval_one_eq_natCard_pic0`](thm.html#AlgebraicCurve.LPolynomial_eval_one_eq_natCard_pic0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_divisor_degree_eq_one_of_finite.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.exists_divisor_degree_eq_one_of_finite
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) :
    ∃ D : AlgebraicCurve.Divisor k F, AlgebraicCurve.Divisor.degree D = 1 := by sorry
