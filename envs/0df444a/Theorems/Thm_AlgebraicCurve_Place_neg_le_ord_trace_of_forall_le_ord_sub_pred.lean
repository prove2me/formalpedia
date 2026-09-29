-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_sub_pred
-- name    : AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord_sub_pred
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/8d804552-294b-5e96-950b-3a01358daf07
-- title:
--   Trace floor with the different gain at a place
-- statement:
--   Let $k$ be an algebraically closed field and let $F$, $F'$ be fields that are algebras over $k$, each satisfying `IsCurveOver k`: every nonzero element has a degree-zero principal divisor, every place has residue field finite over $k$, and $\Omega_{F/k}$ (resp. $\Omega_{F'/k}$) is free of rank one. Here a place of $F$ over $k$ is a valuation subring of $F$ containing the image of $k$, different from $F$ itself, and a principal ideal ring; $\operatorname{ord}_v$ denotes minus the logarithm of the associated adic valuation. Let $\varphi\colon F \to F'$ be a $k$-algebra homomorphism which is integral, and view $F'$ as an $F$-algebra through $\varphi$; assume $F'$ is finite as an $F$-module and separable over $F$. Let $x$ be a place of $F$, and let $S$ be a finite set of places of $F'$ characterised by the property that $y \in S$ if and only if the contraction of $y$ along $\varphi$ equals $x$. For a place $y$ of $F'$, $e_y$ denotes the infimum of the positive integers of the form $\operatorname{ord}_y(\varphi(f))$ with $f \in F$ nonzero. Let $a \geq 0$ be an integer and $g \in F'$ with $\operatorname{ord}_y(g) \geq -e_y a - (e_y - 1)$ for every $y \in S$. Then $\operatorname{ord}_x\bigl(\operatorname{Tr}_{F'/F}(g)\bigr) \geq -a$.
--
--   This is the standard bound for the trace of a function along a finite separable map of curves, sharpened by the contribution of the different: the different of the extension of local rings above $x$ is divisible by $\mathfrak{m}_y^{e_y-1}$ at each $y$ above $x$, which buys an extra $e_y - 1$ over the naive estimate $\operatorname{ord}_y(g) \geq -e_y a$ and requires no tameness assumption. It is used in the analysis of Hecke correspondences on modular curves, in particular in the computations [`ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_mem_riemannRochSpace_weightDivisor`](thm.html#ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_mem_riemannRochSpace_weightDivisor) and [`ModularCurve.sum_kaehlerResidueTerm_liftFun_ssHeckeFun_eq`](thm.html#ModularCurve.sum_kaehlerResidueTerm_liftFun_ssHeckeFun_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_sub_pred.lean

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

theorem AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord_sub_pred
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [IsAlgClosed k]
    [IsCurveOver k F] [IsCurveOver k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ) (hsep : SeparableAlong k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ = x)
    (a : ℤ) (ha : 0 ≤ a) (g : F')
    (hg : ∀ y ∈ S, -((Place.ramificationIndexAlong φ y : ℤ) * a) - ((Place.ramificationIndexAlong φ y : ℤ) - 1) ≤ y.ord g) :
    letI := AlgebraicCurve.algebraAlong φ;
    -a ≤ x.ord (Algebra.trace F F' g) := by sorry
