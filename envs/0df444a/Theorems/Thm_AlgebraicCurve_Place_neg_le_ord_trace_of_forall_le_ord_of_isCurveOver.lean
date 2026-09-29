-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_of_isCurveOver
-- name    : AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/99131e92-f71f-55f4-bdfd-a15acdfe5ef3
-- title:
--   Trace preserves pole-order bounds at a place
-- statement:
--   Let $k$ be an algebraically closed field and let $F$, $F'$ be fields equipped with $k$-algebra structures, each satisfying `IsCurveOver k`, i.e. every nonzero function has a principal divisor of degree $0$, every place has residue field finite over $k$, and the module of Kähler differentials over $k$ is free of rank one. Let $\varphi : F \to F'$ be a $k$-algebra homomorphism whose underlying ring homomorphism is integral, such that $F'$, viewed as an $F$-algebra through $\varphi$, is module-finite (`FiniteAlong`) and separable (`SeparableAlong`). Here a place of a field is a valuation subring containing the image of the base field, distinct from the whole field and a principal ideal ring, and $\operatorname{ord}_v f$ is minus the logarithm of the associated adic valuation of $f$, with $\operatorname{ord}_v 0 = 0$. Let $x$ be a place of $F$ and let $S$ be a finite set of places of $F'$ which is exactly the fibre over $x$: a place $y$ of $F'$ lies in $S$ if and only if the pullback of its valuation subring along $\varphi$ is $x$. Let $a \ge 0$ be an integer and $g \in F'$ such that $\operatorname{ord}_y g \ge -e(y)\,a$ for every $y \in S$, where $e(y)$ is the ramification index `Place.ramificationIndexAlong`, the least positive $n$ of the form $\operatorname{ord}_y \varphi(f)$ with $0 \ne f \in F$. Then, with $F'$ an $F$-algebra via $\varphi$, $\operatorname{ord}_x \operatorname{Tr}_{F'/F}(g) \ge -a$.
--
--   This is the standard statement that the trace of a finite separable extension does not worsen pole orders: a function with poles bounded by $e(y)a$ at all places above $x$ has trace with a pole of order at most $a$ at $x$. It is used in the construction of Hecke operators on modular curves, where it bounds the order of the trace of a weight-$2m$ function at a place, in [`ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_mem_riemannRochSpace_weightDivisor`](thm.html#ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_mem_riemannRochSpace_weightDivisor) and [`ModularCurve.sum_kaehlerResidueTerm_liftFun_ssHeckeFun_eq`](thm.html#ModularCurve.sum_kaehlerResidueTerm_liftFun_ssHeckeFun_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve

theorem AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord_of_isCurveOver
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [IsAlgClosed k]
    [IsCurveOver k F] [IsCurveOver k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ) (hsep : SeparableAlong k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ = x)
    (a : ℤ) (ha : 0 ≤ a) (g : F') (hg : ∀ y ∈ S, -((Place.ramificationIndexAlong φ y : ℤ) * a) ≤ y.ord g) :
    letI := AlgebraicCurve.algebraAlong φ;
    -a ≤ x.ord (Algebra.trace F F' g) := by sorry
