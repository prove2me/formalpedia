-- Prove2me | Theorems.Thm_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq
-- name    : AlgebraicCurve.finite_and_finrank_polarDifferentials_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/96fff16c-e80b-5c91-8a02-b77c762b1eb9
-- title:
--   Dimension of differentials with simple poles on S
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and is a curve over $K$ in the project's sense: every nonzero $f \in F$ has a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place and $\deg D = 0$, each place has residue field finite over $K$, and $\Omega[F/K]$ is free of rank $1$ over $F$; here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring. Assume in addition that $F/K$ has canonical divisors, i.e. every nonzero $\omega \in \Omega[F/K]$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v$ of the coefficient of $\omega$ at $v$ for all $v$. Let $S$ be a nonempty finite set of places of $F/K$, and let $\Omega^1(S)$ be the $K$-subspace of those $\omega \in \Omega[F/K]$ such that for $v \notin S$ one has $\omega = f \cdot d\pi_v$ with $f$ in the valuation ring of $v$, and for $v \in S$ one has $\omega = f \cdot d\pi_v$ with $\pi_v f$ in that valuation ring. Then $\Omega^1(S)$ is a finite $K$-module and its $K$-rank equals $g + \#S - 1$, where $g$ is the genus of $F/K$, defined as $\lfloor(\deg W + 2)/2\rfloor$ for a canonical divisor $W$ (and $0$ if $\Omega[F/K]$ vanishes), the subtraction being truncated subtraction of natural numbers.
--
--   This is the classical computation $\dim_K H^0(X, \Omega^1(S)) = g + \#S - 1$ for a nonempty finite set $S$ of points on a curve over an algebraically closed field, obtained from Riemann–Roch applied to $W + S$; the hypothesis that $S$ be nonempty is essential, the value for $S = \emptyset$ being $g$. It supplies the dimension count used by the results on the residue map $\Omega^1(S) \to K^S$, in particular the existence of differentials in $\Omega^1(S)$ with prescribed residues summing to zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.finite_and_finrank_polarDifferentials_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (S : Finset (AlgebraicCurve.Place K F)) (hS : S.Nonempty) :
    Module.Finite K ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) ∧
      Module.finrank K ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) =
        AlgebraicCurve.genus K F + S.card - 1 := by sorry
