-- Prove2me | Theorems.Thm_AutomorphicForm_AdelicTracePushforward_trace_traceFibre
-- name    : AutomorphicForm.AdelicTracePushforward.trace_traceFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/4237ff46-bb8b-5571-a5fd-77c15f480859
-- title:
--   Trace of trace-adapted adelic coordinates equals r
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $r$ be an adele of $K$, and let $w$ be a family of adeles of $K$ indexed by $\mathrm{Fin}$ of $\dim_K \ker(\operatorname{Tr}_{L/K})$, where $\operatorname{Tr}_{L/K}$ is the $K$-linear trace map $L \to K$. Give the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L` the $\mathbb{A}_K$-algebra structure induced by the ring homomorphism $\beta =$ [`M4aHerbrand.Bridge.genuineβ K L`](def/M4aHerbrand_GenuineBeta.html#L14) $\colon \mathbb{A}_K \to \mathbb{A}_L$, which is the $\beta$-component of the base-change datum [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87); that datum also records that $\beta$ is compatible with the maps $K \to \mathbb{A}_K$, $L \to \mathbb{A}_L$ and $K \to L$, and that the induced map $\mathbb{A}_K \otimes_K L \to \mathbb{A}_L$ is an $\mathbb{A}_K$-algebra isomorphism sending $1 \otimes \ell$ to the image of $\ell$ in $\mathbb{A}_L$. The assertion is that the $\mathbb{A}_K$-linear trace of the element $$\operatorname{traceFibre}(r,w) \;=\; \beta(r)\cdot \bigl([L:K]^{-1}\bigr)_{\mathbb{A}_L} \;+\; \sum_i \beta(w_i)\cdot (c_i)_{\mathbb{A}_L} \in \mathbb{A}_L,$$ where $c$ is the basis `Module.finBasis` of the trace-zero subspace $\ker(\operatorname{Tr}_{L/K}) \subseteq L$ and elements of $L$ are mapped into $\mathbb{A}_L$ by the structure map, equals $r$.
--
--   This is the bookkeeping identity attached to trace-adapted coordinates on $\mathbb{A}_L$ relative to $\mathbb{A}_K$: the fibre of $\operatorname{Tr}_{\mathbb{A}_L/\mathbb{A}_K}$ above a prescribed adele $r$ is parametrised by the remaining coordinates $w$. It is used in the integration step for twisted Bruhat data, where a non-vanishing condition on a trace is converted into the condition $r \neq 0$ on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_AdelicTracePushforward_trace_traceFibre.lean

import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.AdelicTracePushforward.trace_traceFibre
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (r : AdeleRing (𝓞 K) K) (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :
    letI := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toAlgebra
    Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L)
      (AutomorphicForm.AdelicTracePushforward.traceFibre K L r w) = r := by sorry
