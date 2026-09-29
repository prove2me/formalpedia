-- Prove2me | Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
-- name    : AlgebraicCurve.stichtenothGenusExists_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/78654643-12b2-5eb8-9923-a67195bfef37
-- title:
--   Existence of the Stichtenoth genus for a curve over a perfect field
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ perfect, $F$ essentially of finite type over $K$, and suppose $F$ is a curve over $K$ in the sense of `IsCurveOver`: every nonzero $f \in F$ has a divisor $D$ with $D(v) = \operatorname{ord}_v f$ at each place $v$ and $\deg D = 0$; for every place $v$ (a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring) the residue field of $v$ is a finite $K$-module; and $\Omega_{F/K}$ is a free $F$-module of rank one. Assume moreover `ConstantsAreBase K F`, i.e. the Riemann–Roch space $L(0)$ of the zero divisor equals the image of $K$ in $F$. The conclusion `StichtenothGenusExists K F` asserts three things: there exists at least one place of $F$ over $K$; $L(0)$ is finite-dimensional over $K$; and there are an integer $\gamma$ and a divisor $D_0$ (a finitely supported $\mathbb{Z}$-valued function on places) such that $L(D_0)$ is finite-dimensional over $K$, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$, where $\ell$ is the dimension invariant `ell` of the Riemann–Roch space.
--
--   This is the existence of the genus in Stichtenoth's formulation, the maximum of $\deg D - \ell(D)$ over all divisors, for an arbitrary one-variable function field over a perfect field whose field of constants is the base field; the hypotheses involve no auxiliary rational subfield. It is the form in which the genus is used throughout the divisor-theoretic development of curves in the project, for instance in the study of $\operatorname{Pic}^0$ and of constant reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem stichtenothGenusExists_of_isCurveOver {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F := by sorry
