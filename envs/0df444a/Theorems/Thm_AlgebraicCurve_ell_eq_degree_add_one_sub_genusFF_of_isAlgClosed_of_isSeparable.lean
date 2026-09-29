-- Prove2me | Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
-- name    : AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/1ae50d15-37c4-5a9d-9054-09cdc9f3f89e
-- title:
--   Riemann–Roch equality for deg D ≥ 2g-1
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field equipped with a $k$-algebra structure. Suppose there is an element $x \in F$ transcendental over $k$ such that $F$ is finite-dimensional over the intermediate field $k\langle x\rangle =$ `IntermediateField.adjoin k {x}` and separable over it. A place of $F/k$ is a valuation subring of $F$ containing the image of $k$, distinct from $F$ itself and a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$, and its degree is $\sum_v D(v)\,\deg v$. Write $\ell(D)$ for the $k$-dimension of the Riemann–Roch space $L(D)$ and $g =$ `genusFF k F` for the $k$-dimension of $H^1$ of the zero divisor. The assertion is: for every divisor $D$ of $F/k$ with $\deg D \ge 2g - 1$, one has, as an identity of integers,
--   $$\ell(D) = \deg D + 1 - g.$$
--
--   This is the Riemann–Roch theorem in its sharp form above the threshold $\deg D > 2g - 2$, for a function field in one variable over an algebraically closed constant field, stated with the hypotheses in the convenient shape ($x$ transcendental, $F/k(x)$ finite and separable) rather than as a bundle of curve-structure instances. It is the dimension-counting input used wherever effective divisors of large degree must be shown to have Riemann–Roch spaces of the expected size, for instance in the glueing and base-point-freeness arguments for semistable coverings cited downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable.lean

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

theorem AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (D : Divisor k F) (hD : 2 * (genusFF k F : ℤ) - 1 ≤ D.degree) :
    (ell D : ℤ) = D.degree + 1 - (genusFF k F : ℤ) := by sorry
