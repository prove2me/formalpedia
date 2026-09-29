-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential
-- name    : AlgebraicCurve.Place.ordDiff_eq_ordDifferential
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/09c76274-63ea-5dda-a3a7-31d65caf24cb
-- title:
--   The two orders of a differential at a place agree
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ of characteristic zero, $F$ essentially of finite type over $K$, and suppose $F/K$ satisfies the curve axioms of `IsCurveOver`: every nonzero $f \in F$ has a divisor of degree $0$ whose value at each place $v$ is $\mathrm{ord}_v f$, each residue field $\mathcal{O}_v/\mathfrak{m}_v$ is finite-dimensional over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Let $v$ be a place of $F/K$ (a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring) and let $\omega \in \Omega_{F/K}$. The assertion is the equality of two integers attached to $\omega$ at $v$: on one side $\mathrm{ord}_v$ of the coefficient $g$ in a representation $\omega = g \cdot \mathrm{d}t$, where $t$ is the element chosen by `uniformizer_alt` from those with $\mathrm{ord}_v t = 1$ (and $g$, as in `diffCoeff`, is a chosen solution, $0$ if none exists); on the other side $\mathrm{ord}_v$ of the coefficient chosen by `differentialCoeff` in a representation $\omega = f \cdot \mathrm{dCoord}_v$.
--
--   This is the well-definedness of the order of a differential at a place in the form needed here: the two formalisations of that order, one computed against a chosen element of valuation $1$ and one against the distinguished coordinate differential $\mathrm{dCoord}_v$, define the same integer. It is used to transfer results between the two settings, for instance in the identification of regular differentials and in the computations of orders of Wronskians on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ordDiff_eq_ordDifferential {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω := by sorry
