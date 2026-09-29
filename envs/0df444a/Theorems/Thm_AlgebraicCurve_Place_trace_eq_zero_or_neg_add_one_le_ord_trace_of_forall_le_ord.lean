-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord
-- name    : AlgebraicCurve.Place.trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/f250468b-a96c-5cd9-8bf4-8c119c195651
-- title:
--   Strict trace bound along places over a fixed place
-- statement:
--   Let $k$ be an algebraically closed field and let $F$, $F'$ be fields with $k$-algebra structures such that each of $F/k$ and $F'/k$ is a curve in the sense of the project's class: principal divisors exist (every nonzero $f$ has a degree-zero divisor recording its orders $\operatorname{ord}_v f$ at all places), every place has residue field finite over $k$, and the module of Kähler differentials is free of rank one. Here a place of $F/k$ is a valuation subring of $F$ containing $k$, distinct from $F$, which is a principal ideal ring, and $\operatorname{ord}_v$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation. Let $\varphi\colon F \to F'$ be a $k$-algebra map whose underlying ring map is integral, and assume that, for the $F$-algebra structure on $F'$ given by $\varphi$, $F'$ is a finite $F$-module (`FiniteAlong`) and is separable over $F$ (`SeparableAlong`). Let $x$ be a place of $F/k$ and let $S$ be a finite set of places of $F'/k$ which, by hypothesis, consists exactly of those $y$ whose restriction along $\varphi$ (the comap of $y$ under $\varphi$) equals $x$. For $y$ a place of $F'$, $e(y) :=$ `Place.ramificationIndexAlong` $\varphi\ y$ is the infimum of the set of natural numbers $n>0$ such that $\operatorname{ord}_y(\varphi f) = n$ for some nonzero $f \in F$. Let $a \in \mathbb{Z}$ and $g \in F'$ satisfy $\operatorname{ord}_y g \ge -e(y)\,a + 1$ for every $y \in S$. Then, for the trace of the $F$-algebra $F'$ determined by $\varphi$, either $\operatorname{Tr}_{F'/F}(g) = 0$ or $\operatorname{ord}_x\bigl(\operatorname{Tr}_{F'/F}(g)\bigr) \ge -a + 1$.
--
--   This is the strict form of the local trace estimate for a finite separable extension of one-variable function fields: raising the lower bound on the order of $g$ by one at every place above $x$ raises by one the lower bound on the order of its trace at $x$, the disjunction accommodating the convention $\operatorname{ord}(0)=0$. It is used in the construction of the Hecke action on differentials on modular curves, in establishing additivity and $k$-linearity of the relevant Hecke operator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem AlgebraicCurve.Place.trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [IsAlgClosed k]
    [IsCurveOver k F] [IsCurveOver k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ) (hsep : SeparableAlong k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ = x)
    (a : ℤ) (g : F') (hg : ∀ y ∈ S, -((Place.ramificationIndexAlong φ y : ℤ) * a) + 1 ≤ y.ord g) :
    letI := AlgebraicCurve.algebraAlong φ;
    Algebra.trace F F' g = 0 ∨ -a + 1 ≤ x.ord (Algebra.trace F F' g) := by sorry
