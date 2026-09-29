-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos
-- name    : AlgebraicCurve.Place.exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/79e2a4ea-afe5-5cef-94c9-d7e727556af1
-- title:
--   All but finitely many fibres of x are unramified
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure making it a curve over $K$ in the sense of the project's `IsCurveOver` class: every nonzero $f \in F$ has a divisor $D$ with $D(v) = \operatorname{ord}_v f$ at every place $v$ and $\deg D = 0$; each place has residue field finite over $K$; and $\Omega_{F/K}$ is free of rank one over $F$. Here a place $v$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring, and $\operatorname{ord}_v(f)$ is minus the logarithm of the value of $f$ under the $\mathbb{Z}^{m0}$-valued valuation attached to the height-one spectrum point of $v$, so that a uniformiser has $\operatorname{ord}_v = 1$. Let $x \in F$ be transcendental over $K$, and assume that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}` and separable over it. The conclusion is that there is a finite subset $C \subseteq K$ such that for every $c \in K$ with $c \notin C$ and every place $v$ of $F$ over $K$, if $\operatorname{ord}_v(x - c) > 0$ then $\operatorname{ord}_v(x - c) = 1$.
--
--   This is the statement that the separable map $x \colon F \supseteq K(x)$ has only finitely many critical values: all but finitely many fibres $x = c$ consist of simple zeros, equivalently only finitely many places ramify over $\mathbb{P}^1$ and each lies over one value of $x$. It supports the finiteness of the set of places where the fibre cardinality of $x$ differs from the degree, a generation statement for subfield closures, and the multiplicity-one argument used to control inertia in the modular-curve part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
    (x : F) (hx : Transcendental K x)
    (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ C : Finset K, ∀ c : K, c ∉ C → ∀ v : AlgebraicCurve.Place K F,
      0 < v.ord (x - algebraMap K F c) → v.ord (x - algebraMap K F c) = 1 := by sorry
