-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt
-- name    : AlgebraicCurve.Place.mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/05cb971b-cb9c-5076-b9da-68659161a762
-- title:
--   Trace at a place: Tr(g)(x)=sum_{y∣ x}e(y∣ x) g(y)
-- statement:
--   Let $k$ be an algebraically closed field and let $F$, $F'$ be fields, each a $k$-algebra satisfying `IsCurveOver k ·`, i.e. every nonzero element has a principal divisor of degree $0$, each place has residue field finite over $k$, and the module of Kähler differentials over $k$ is free of rank one. Here a place of $F$ over $k$ is a valuation subring of $F$ containing the image of $k$, different from $F$ itself, and a principal ideal ring. Let $\varphi : F \to F'$ be a $k$-algebra map whose underlying ring map is integral, regarded as giving $F'$ the structure of an $F$-algebra; assume $F'$ is a finite and separable $F$-algebra for this structure. Let $x$ be a place of $F$, and let $S$ be a finite set of places of $F'$ such that a place $y$ of $F'$ belongs to $S$ exactly when the contraction of $y$ along $\varphi$ (the preimage valuation subring) equals $x$. Let $g \in F'$ lie in the valuation subring of every $y \in S$. Then $\operatorname{Tr}_{F'/F}(g)$ lies in the valuation subring of $x$, and its value at $x$ satisfies $x.\mathrm{evalAt}(\operatorname{Tr}_{F'/F} g) = \sum_{y \in S} e_y \cdot y.\mathrm{evalAt}(g)$ in $k$, where $e_y$ is the image in $k$ of the ramification index of $y$ over $F$, namely the least $n > 0$ for which $\operatorname{ord}_y(\varphi f) = n$ for some nonzero $f \in F$, and $v.\mathrm{evalAt}(h)$ denotes the element of $k$ obtained from the residue of $h$ in the residue field of $v$ via an inverse of $k \to \kappa(v)$ (and $0$ when $h$ is not in the valuation subring of $v$).
--
--   This is the local trace formula for a finite separable extension of function fields over an algebraically closed base: the value at $x$ of the trace of a function integral on the whole fibre is the sum of its values over the fibre, weighted by ramification indices; residue degrees are $1$ because $k$ is algebraically closed. It is used in the computation of Hecke operators on supersingular values, in [`ModularCurve.SSHeckeV2.lead_trace_heckeBetaC_mul_pow_eq_ssHeckeFun_of_map`](thm.html#ModularCurve.SSHeckeV2.lead_trace_heckeBetaC_mul_pow_eq_ssHeckeFun_of_map) and [`ModularCurve.SSHeckeV2.ssHeckeFun_bMul_eq_smul_bMul_ssHeckeFun`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_bMul_eq_smul_bMul_ssHeckeFun).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve KaehlerDifferential

theorem AlgebraicCurve.Place.mem_and_evalAt_trace_eq_sum_ramificationIndexAlong_smul_evalAt
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [IsAlgClosed k]
    [IsCurveOver k F] [IsCurveOver k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ) (hsep : SeparableAlong k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ = x)
    (g : F') (hg : ∀ y ∈ S, g ∈ y.toValuationSubring) :
    letI := AlgebraicCurve.algebraAlong φ
    Algebra.trace F F' g ∈ x.toValuationSubring ∧
      x.evalAt (Algebra.trace F F' g) = ∑ y ∈ S, ((Place.ramificationIndexAlong φ y : ℕ) : k) • y.evalAt g := by sorry
