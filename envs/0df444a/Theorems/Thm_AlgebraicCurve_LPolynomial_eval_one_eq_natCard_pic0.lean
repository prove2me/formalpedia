-- Prove2me | Theorems.Thm_AlgebraicCurve_LPolynomial_eval_one_eq_natCard_pic0
-- name    : AlgebraicCurve.LPolynomial_eval_one_eq_natCard_pic0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/d1715ce3-9a9e-5fdc-a903-a793d6ebf6c5
-- title:
--   Class number formula: L(1)=#Pic⁰ for function fields
-- statement:
--   Let $k$ be a finite field and $F$ a field equipped with a $k$-algebra structure which is a curve over $k$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ has a divisor recording its orders $v.\mathrm{ord}\,f$ at all places and of degree $0$, each place $v$ of $F/k$ (a proper valuation subring of $F$ containing $k$ whose ideals are principal) has residue field finite over $k$, and the module of Kähler differentials $\Omega_{F/k}$ is free of rank one over $F$; assume also that $F$ is of essentially finite type over $k$ and that the constants are the base field in the sense that the Riemann–Roch space of the zero divisor equals the image of $k$ under $\mathrm{algebraMap}$. Let $L \in \mathbb{Z}[X]$ be a polynomial whose associated power series satisfies $$(1-X)\bigl(1-\#k\cdot X\bigr)\sum_{n\ge 0} A_n X^n = L(X) \quad\text{in } \mathbb{Z}[[X]],$$ where $A_n$ is the number of divisors $D$ of $F/k$ with $0 \le D$ and $\deg D = n$ (degrees being computed from the residue degrees of the places). Then $L(1)$ equals the cardinality of $\mathrm{Pic}^0(F/k)$, the group of degree-zero divisors modulo the subgroup of principal divisors, cast into $\mathbb{Z}$.
--
--   This is the class number formula for a function field of one variable over a finite field: the $L$-polynomial, defined by the rationality identity for the zeta function, takes the value $\#\mathrm{Pic}^0$ at $t=1$. It is stated for any polynomial satisfying that identity, so that it can be combined with the rationality theorem in whatever form is at hand, and it feeds into [`AlgebraicCurve.eval_one_eq_natCard_pic0_of_natCard_fixedPoints_restrictAlong_eq`](thm.html#AlgebraicCurve.eval_one_eq_natCard_pic0_of_natCard_fixedPoints_restrictAlong_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_LPolynomial_eval_one_eq_natCard_pic0.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.LPolynomial_eval_one_eq_natCard_pic0
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) (L : Polynomial ℤ)
    (hL : (1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k : ℤ) * PowerSeries.X) *
          PowerSeries.mk (fun n : ℕ =>
            (Nat.card {D : AlgebraicCurve.Divisor k F //
                0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = (n : ℤ)} : ℤ)) =
        (L : PowerSeries ℤ)) :
    L.eval 1 = Nat.card (AlgebraicCurve.Pic0 k F) := by sorry
