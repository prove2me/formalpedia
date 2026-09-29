-- Prove2me | Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental
-- name    : AlgebraicCurve.finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/8883fed7-e8fd-5bd3-a265-545d6615724e
-- title:
--   L(0) is finite-dimensional and ℓ(0)=1 over algebraically closed k
-- statement:
--   Let $k$ be an algebraically closed field and let $F$ be a field equipped with a $k$-algebra structure. Let $x \in F$ be transcendental over $k$, and assume that $F$ is finite-dimensional as a vector space over the intermediate field $k\langle x\rangle =$ `IntermediateField.adjoin k {x}`. The conclusion is the conjunction of two assertions about the zero divisor, the zero element of `Divisor k F` $=$ (`Place k F` $\to_{f0}$ $\mathbb{Z}$), where a place of $F/k$ is a valuation subring of $F$ that contains the image of $k$, is not all of $F$, and is a principal ideal ring. First, the space $\mathrm{LSpace}(0) = \{f \in F : v(f) \le 1 \text{ for every place } v\}$, i.e. the set of elements lying in every such valuation subring, which is a $k$-submodule of $F$, is finite-dimensional over $k$. Second, $\ell(0) = \operatorname{finrank}_k \mathrm{LSpace}(0) = 1$; together with the fact that the image of $k$ lies in $\mathrm{LSpace}(0)$ this says that the only elements of $F$ without poles are the constants. No separability hypothesis is imposed on $F/k\langle x\rangle$.
--
--   This is the statement that the field of constants of a function field over an algebraically closed base field is the base field itself, in the form $L(0) = k$, for the light presentation of a curve as a finite extension of a rational function field. It feeds the divisor-theoretic and Riemann–Roch machinery used later, and is cited in the analysis of Picard groups of curves and in the construction of separating and regular functions on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped IntermediateField

theorem AlgebraicCurve.finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    FiniteDimensional k ↥(LSpace (0 : Divisor k F)) ∧ ell (0 : Divisor k F) = 1 := by sorry
