-- Prove2me | Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
-- name    : AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/e7ba4d46-47a9-5639-b062-3daade338787
-- title:
--   One-variable function fields over perfect fields are curves
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and suppose $K$ is perfect. Assume there is an element $x \in F$ transcendental over $K$ such that $F$ is finite-dimensional over the intermediate field $K(x)$ obtained by adjoining $x$. The conclusion is that the pair $(K,F)$ satisfies [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15), that is: (i) $F/K$ has principal divisors, meaning that for every $f \in F$ with $f \neq 0$ there is a divisor $D$ of $F/K$ whose coefficient at each place $v$ equals $v.\mathrm{ord}\, f$ and whose degree is $0$ — here a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring; (ii) for every place $v$ of $F/K$ the residue field of that valuation subring is a finite-dimensional $K$-module; and (iii) the module of Kähler differentials $\Omega_{F/K}$ is a free $F$-module with $\operatorname{finrank}_F \Omega_{F/K} = 1$. No separability assumption on $F$ over $K(x)$ is imposed.
--
--   This is the statement that a function field of transcendence degree one over a perfect constant field carries the curve package used throughout the project: finiteness of residue degrees, existence of degree-zero principal divisors, and a one-dimensional space of differentials. It serves as the standard source of `IsCurveOver` instances, and is invoked by the body of results on places, regularity, poles and residues built on top of that package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    AlgebraicCurve.IsCurveOver K F := by sorry
