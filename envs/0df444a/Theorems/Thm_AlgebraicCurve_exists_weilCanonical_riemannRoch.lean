-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
-- name    : AlgebraicCurve.exists_weilCanonical_riemannRoch
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/b3f1ddf5-d7e3-59fd-8518-58631f485026
-- title:
--   Riemann–Roch with a Weil canonical divisor
-- statement:
--   Let $K$ be a perfect field and $F$ a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and satisfies [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15); the latter asserts that every nonzero $f \in F$ has a principal divisor, namely a finitely supported $\mathbb Z$-valued function on the places of $F/K$ whose value at each place $v$ is $v.\mathrm{ord}\,f$ and whose degree is $0$, that for each place $v$ the residue field of $v$ is a finite $K$-module, and that the module of Kähler differentials $\Omega[F/K]$ is free of rank $1$ over $F$. Here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring, and a divisor is a finitely supported $\mathbb Z$-valued function on the set of places, the degree being the sum of its values weighted by the degrees of the places. Assume moreover `ConstantsAreBase K F`: the Riemann–Roch space $\mathcal L(0)$ of the zero divisor equals the image of $K$ in $F$. Then there is a divisor $W$ of $F/K$ such that for every divisor $D$ one has, as an identity of integers,
--   $$\ell(D) - \ell(W - D) = \deg D + 1 - g,$$
--   where $\ell(E)$ denotes the $K$-dimension ($\mathrm{finrank}$) of the Riemann–Roch space $\mathcal L(E)$ and $g$ is `genusFF K F`, defined as the $K$-dimension of the space `H1 (0)` attached to the zero divisor. Since $\ell$ is a `finrank`, the statement carries no separate finiteness assertion.
--
--   This is the Riemann–Roch theorem for an algebraic function field in one variable with perfect full constant field $K$, the divisor $W$ being a canonical (Weil-differential) divisor; taking $D = 0$ and $D = W$ yields $\ell(W) = g$ and $\deg W = 2g - 2$. It is used in the construction of the $L$-polynomial of a function field over a finite field ([`AlgebraicCurve.exists_LPolynomial_of_finite`](thm.html#AlgebraicCurve.exists_LPolynomial_of_finite)) and in the analysis of models and sections on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.exists_weilCanonical_riemannRoch
    (K F : Type*) [Field K] [PerfectField K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : AlgebraicCurve.ConstantsAreBase K F) :
    ∃ W : AlgebraicCurve.Divisor K F, ∀ D : AlgebraicCurve.Divisor K F,
      (AlgebraicCurve.ell D : ℤ) - (AlgebraicCurve.ell (W - D) : ℤ) =
        AlgebraicCurve.Divisor.degree D + 1 - (AlgebraicCurve.genusFF K F : ℤ) := by sorry
