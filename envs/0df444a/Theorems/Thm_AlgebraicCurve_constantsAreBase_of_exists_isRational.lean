-- Prove2me | Theorems.Thm_AlgebraicCurve_constantsAreBase_of_exists_isRational
-- name    : AlgebraicCurve.constantsAreBase_of_exists_isRational
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/e5935f1d-f6fa-5aab-a3ff-4940601a9231
-- title:
--   Constants are the base field, given a rational place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume the class [`AlgebraicCurve.HasPrincipalDivisors K F`](def/AlgebraicCurve_DivisorClassGroup.html#L217): every nonzero $f \in F$ admits a divisor $D$ (a finitely supported $\mathbb{Z}$-valued function on the places of $K$ in $F$) with $D(v) = \operatorname{ord}_v(f)$ for all places $v$ and with $\deg D = 0$, the degree being $\sum_v D(v)\,\deg v$ where $\deg v = \operatorname{finrank}_K$ of the residue field of $v$. Here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring. Suppose given one place $v_0$ such that the structure map $K \to \kappa(v_0)$ onto the residue field of $v_0$ is surjective (the predicate [`AlgebraicCurve.Place.IsRational`](def/AlgebraicCurve_PlaceEvaluation.html#L18)), and such that $\deg v_0 \neq 0$. The conclusion is [`AlgebraicCurve.ConstantsAreBase K F`](def/AlgebraicCurve_AdelicIndex.html#L45), namely that the Riemann–Roch space of the zero divisor, $L(0) \subseteq F$, equals the range of the $K$-linear map $K \to F$; that is, the elements of $F$ with no poles at any place are exactly the constants coming from $K$.
--
--   This is the standard statement that the field of constants of a function field is the base field, as soon as there exists a rational place of nonzero degree. It is used to supply the `ConstantsAreBase` hypothesis in the Riemann–Roch corollaries of the project, via the specialisations [`AlgebraicCurve.constantsAreBase_of_deg_eq_one`](thm.html#AlgebraicCurve.constantsAreBase_of_deg_eq_one) and [`AlgebraicCurve.constantsAreBase_of_isAlgClosed`](thm.html#AlgebraicCurve.constantsAreBase_of_isAlgClosed), and ultimately in the Serre-duality pairing statement for curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_constantsAreBase_of_exists_isRational.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.constantsAreBase_of_exists_isRational {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (v₀ : AlgebraicCurve.Place K F) (hrat : v₀.IsRational) (hdeg : v₀.deg ≠ 0) :
    AlgebraicCurve.ConstantsAreBase K F := by sorry
