-- Prove2me | Theorems.Thm_AlgebraicCurve_traceIntegralAlong_of_separableAlong
-- name    : AlgebraicCurve.traceIntegralAlong_of_separableAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/d50e3132-cc03-50a4-abe2-0d48da805322
-- title:
--   Trace integrality along a finite separable extension of fields
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, and let $\varphi : F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral. Assume `FiniteAlong K φ`, i.e. that $F'$ is a finite module over $F$ for the algebra structure induced by $\varphi$, and `SeparableAlong K φ`, i.e. that $F'$ is separable over $F$ for that same structure. Then `TraceIntegralAlong φ hφ` holds: for every place $v$ of $F$ over $K$ — a valuation subring of $F$ which contains the image of $K$, is not all of $F$, and is a principal ideal ring — and every $f' \in F'$ with the property that $f'$ belongs to the valuation subring of every place $w$ of $F'$ over $K$ whose restriction along $\varphi$ (the place of $F$ obtained by pulling $w$ back through $\varphi$, using integrality of $\varphi$) equals $v$, the element $\operatorname{Tr}_{F'/F}(f')$, i.e. the image of $f'$ under `traceFunAlong φ` (the $K$-linear map given by the algebra trace of $F'$ over $F$ along $\varphi$), lies in the valuation subring of $v$.
--
--   This is the statement that the trace of a finite separable extension of function fields carries elements integral at all places above $v$ into the local ring at $v$; it discharges the `TraceIntegralAlong` hypothesis used to define the trace (norm) map on Čech $H^1$ of a two-chart cover. It is invoked in the local estimates [`AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord`](thm.html#AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord) and its variant over a curve, and in the construction of the degeneracy trace on function fields of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_traceIntegralAlong_of_separableAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem traceIntegralAlong_of_separableAlong {K : Type*} {F : Type*} {F' : Type*}
    [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) :
    TraceIntegralAlong φ hφ := by sorry
