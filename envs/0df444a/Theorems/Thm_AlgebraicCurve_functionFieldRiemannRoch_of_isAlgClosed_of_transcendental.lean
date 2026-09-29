-- Prove2me | Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
-- name    : AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/e4506fd1-2bf2-5a7d-b0fb-ffbfe6c89c40
-- title:
--   Riemann–Roch for one-variable function fields over algebraically closed fields
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure, and suppose there is an element $x \in F$ transcendental over $K$ such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. The conclusion is the proposition [`AlgebraicCurve.FunctionFieldRiemannRoch K F`](def/AlgebraicCurve_RiemannRochRows.html#L44), which asserts: whenever $F/K$ is given the curve package — `IsCurveOver K F`, i.e. principal divisors together with finiteness of $v$.`ResidueField` over $K$ at every place $v$ and freeness of $\Omega[F/K]$ over $F$ of rank $1$; `HasCanonicalDivisor`, i.e. for each nonzero $\omega \in \Omega[F/K]$ there is a divisor whose value at each place $v$ is $v$.`ordDifferential` $\omega$; and `DCoordGenerates` at every place $v$, i.e. $v$.`dCoord` spans $\Omega[F/K]$ over $F$ — then for every nonzero $\omega \in \Omega[F/K]$ and every divisor $D$ (a finitely supported $\mathbb{Z}$-valued function on the places of $F/K$, a place being a proper valuation subring of $F$ containing $K$ whose ring structure is a principal ideal ring) one has $$\mathrm{ell}(D) - \mathrm{ell}((\omega) - D) = \deg D + 1 - g,$$ where $(\omega)$ is the chosen canonical divisor `canonicalDivisorOf` of $\omega$, $\deg D = \sum_v D(v) \cdot v.\mathrm{deg}$, `ell` is the natural-number invariant attached to a divisor (its Riemann–Roch dimension), and $g$ is `genus K F`, namely $\lfloor(\deg(\omega_0) + 2)/2\rfloor$ for a chosen nonzero differential $\omega_0$ when one exists and $0$ otherwise.
--
--   This is the Riemann–Roch theorem for an algebraic function field of one variable over an algebraically closed constant field, stated from bare hypotheses: only transcendence of one element and finiteness of $F$ over $K(x)$ are assumed, all curve-structure data being derived rather than hypothesised. It feeds the divisor-theoretic and Picard-group results of the project, such as the computation of the order of the $p$-torsion of $\mathrm{Pic}^0$ and the bounds on Riemann–Roch dimensions under place reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F := by sorry
