-- Prove2me | Theorems.Thm_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts
-- name    : AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_sum_lifts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/1f7a3144-39e8-5174-bf8f-79dfb2b5f49f
-- title:
--   Trace of differentials at a geometric point is a sum over lifts
-- statement:
--   Let $K$, $F$, $F'$ and $E$ be fields, each of $F$, $F'$, $E$ a $K$-algebra, with $E$ algebraically closed, and let $\varphi\colon F \to F'$ be a homomorphism of $K$-algebras. Assume `FiniteAlong K φ`, i.e. that $F'$ is a finite module over $F$ for the $F$-algebra structure on $F'$ given by $\varphi$, and `SeparableAlong K φ`, i.e. that $F'$ is separable over $F$ for that same structure. Let $e\colon F \to E$ be a homomorphism of $K$-algebras, and let $S$ be a finite set of $K$-algebra homomorphisms $F' \to E$ whose members are characterised by the hypothesis that $\sigma \in S$ if and only if $\sigma \circ \varphi = e$. Then for every Kähler differential $\omega' \in \Omega_{F'/K}$ one has, in $\Omega_{E/K}$, $$\mathrm{pullbackAlong}(e)\bigl(\mathrm{traceAlong}(\varphi)(\omega')\bigr) = \sum_{\sigma \in S} \mathrm{pullbackAlong}(\sigma)(\omega'),$$ where $\mathrm{pullbackAlong}(\tau)$ is the functorial $K$-linear map on Kähler differentials induced by a $K$-algebra homomorphism $\tau$, and $\mathrm{traceAlong}(\varphi)$ is the $K$-linear map $\Omega_{F'/K} \to \Omega_{F/K}$ defined, when $F'$ is separable over $F$ along $\varphi$ (as it is here), by inverting the base-change isomorphism $F' \otimes_F \Omega_{F/K} \cong \Omega_{F'/K}$ available for formally étale extensions and then applying $\mathrm{Tr}_{F'/F}$ in the first factor.
--
--   This is the pointwise, or fibrewise, description of the trace of differential forms along a finite separable map of function fields: evaluating the trace at a geometric point $e$ of the base gives the sum of the form over the points of the fibre, i.e. over the $E$-embeddings of $F'$ lifting $e$. It is used in the divisor-class-group part of the development, in the proof that a differential attached to a lifted correspondence vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_sum_lifts
    (K F F' E : Type*) [Field K] [Field F] [Field F'] [Field E]
    [Algebra K F] [Algebra K F'] [Algebra K E] [IsAlgClosed E]
    (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (e : F →ₐ[K] E) (S : Finset (F' →ₐ[K] E)) (hS : ∀ σ : F' →ₐ[K] E, σ ∈ S ↔ σ.comp φ = e)
    (ω' : Ω[F'⁄K]) :
    Differential.pullbackAlong e (Differential.traceAlong φ ω') =
      ∑ σ ∈ S, Differential.pullbackAlong σ ω' := by sorry
