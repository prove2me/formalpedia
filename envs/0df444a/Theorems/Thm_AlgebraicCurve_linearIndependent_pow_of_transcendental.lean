-- Prove2me | Theorems.Thm_AlgebraicCurve_linearIndependent_pow_of_transcendental
-- name    : AlgebraicCurve.linearIndependent_pow_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/91b673f4-9d35-56a2-9173-4ba86b8a9b0f
-- title:
--   Powers of a transcendental element are linearly independent
-- statement:
--   Let $K$ and $A$ be commutative rings with $A$ a $K$-algebra, and let $x \in A$. Assume $x$ is transcendental over $K$, that is, $x$ is not algebraic over $K$: there is no nonzero polynomial $p \in K[X]$ with $p(x) = 0$ (evaluation via the $K$-algebra map $K[X] \to A$ sending $X$ to $x$). The conclusion is that the family of powers $(x^j)_{j \in \mathbb{N}}$, indexed by all natural numbers $j$ including $j = 0$, is linearly independent over $K$ as a family in the $K$-module $A$: every $K$-linear combination of finitely many powers $x^j$ that vanishes has all its coefficients zero. Note that $K$ is only assumed to be a commutative ring, not a field, so linear independence is that of a family in a module over a commutative ring; equivalently, the statement says that the $K$-algebra homomorphism $K[X] \to A$ determined by $X \mapsto x$ is injective, the monomials forming a $K$-basis of $K[X]$.
--
--   This is the standard equivalence between transcendence of an element over the base and injectivity of the associated polynomial evaluation map, in the form of linear independence of the monomials $x^j$. It supplies the independence datum used when a rational function field is presented as a transcendental extension, and is invoked in the construction of integral models and in the computation of the genus of a curve with a principal divisor of the form $P - Q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_linearIndependent_pow_of_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem linearIndependent_pow_of_transcendental {K : Type*} {A : Type*} [CommRing K] [CommRing A] [Algebra K A] {x : A} (hx : Transcendental K x) :
    LinearIndependent K (fun j : ℕ => x ^ j) := by sorry
