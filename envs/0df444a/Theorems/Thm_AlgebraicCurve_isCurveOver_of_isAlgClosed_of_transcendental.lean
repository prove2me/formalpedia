-- Prove2me | Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
-- name    : AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/803f3b0f-03df-506c-8358-bb1db4e07f86
-- title:
--   Curve criterion over an algebraically closed base
-- statement:
--   Let $K$ be an algebraically closed field, let $F$ be a field equipped with a $K$-algebra structure, and let $x \in F$ be transcendental over $K$. Assume that $F$ is finite-dimensional as a vector space over the intermediate field $K(x)$ obtained by adjoining $x$ to $K$ inside $F$. Then `IsCurveOver K F` holds, that is: (i) $F$ has principal divisors over $K$, meaning that for every $f \in F$ with $f \neq 0$ there is a divisor $D$ of $F/K$ whose value at each place $v$ equals the order $v.\mathrm{ord}\, f$ of $f$ at $v$ and whose degree is $0$, where a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$, is different from all of $F$, and is a principal ideal ring; (ii) for every such place $v$ the residue field of the corresponding local ring is a finite $K$-module; and (iii) the module of Kähler differentials $\Omega[F\!\diagup\!K]$ is free over $F$ of rank $1$. Compared with the variant requiring $F$ to be separable over $K(x)$, no separability hypothesis is imposed here.
--
--   This is the working criterion for recognising a field as the function field of a curve over an algebraically closed constant field: a transcendental element with finite residual degree suffices, with no separability condition on $F/K(x)$. It supplies the `IsCurveOver` instance in the many later developments that need it, for instance when the constant field is the algebraically closed residue field of a local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    IsCurveOver K F := by sorry
