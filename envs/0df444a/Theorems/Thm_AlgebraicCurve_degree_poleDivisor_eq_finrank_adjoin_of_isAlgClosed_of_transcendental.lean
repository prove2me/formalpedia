-- Prove2me | Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
-- name    : AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/18dcfd3c-c55b-56e7-b305-233aea765b0a
-- title:
--   Degree of the pole divisor of x equals [F:K(x)]
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure. Let $x \in F$ be transcendental over $K$, and assume $F$ is finite-dimensional as a module over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $D$ be a divisor of $F/K$, that is, a finitely supported integer-valued function on the type `Place K F` of places, a place being a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Suppose $D$ is the pole divisor of $x$, in the sense that for every place $v$ one has $D(v) = \max(0, -\operatorname{ord}_v x)$, where $\operatorname{ord}_v$ is minus the logarithm of the $\mathbb{Z}^{m0}$-valued valuation attached to $v$ through the corresponding height-one prime. Then the degree of $D$, namely the sum $\sum_v D(v)\cdot \deg v$ of its coefficients weighted by the degrees of the places, equals the image in $\mathbb{Z}$ of $\operatorname{finrank}_{K(x)} F$.
--
--   This is the classical statement that the pole divisor $(x)_\infty$ of a non-constant function $x$ has degree $[F:K(x)]$, here in the form where the constant field is algebraically closed. It is the degree-counting input for several later results on genus bounds and on reductions of curves, which invoke it to convert a field degree into a divisor degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) := by sorry
