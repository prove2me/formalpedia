-- Prove2me | Theorems.Thm_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite
-- name    : Algebra.formallyUnramified_iff_traceForm_nondegenerate_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/1498b043-579c-5edd-95d1-3216bc05491f
-- title:
--   Trace-form criterion for unramifiedness of a finite algebra
-- statement:
--   Let $K$ be a field and let $B$ be a commutative ring equipped with a $K$-algebra structure such that $B$ is finite as a $K$-module (both $K$ and $B$ are taken in the same universe). The theorem asserts the equivalence of two conditions: on the one hand, that $B$ is formally unramified over $K$ in the sense of `Algebra.FormallyUnramified`, i.e. for every $K$-algebra $C$ and every square-zero ideal of $C$ any $K$-algebra map $B \to C/I$ lifts in at most one way (equivalently, the module of derivations, or $\Omega_{B/K}$, vanishes); on the other hand, that the trace form of $B$ over $K$, the $K$-bilinear form $(x,y) \mapsto \operatorname{Tr}_{B/K}(xy)$ given by `Algebra.traceForm K B`, is nondegenerate in the sense of `LinearMap.BilinForm.Nondegenerate`, i.e. it has trivial left and right kernels: $\operatorname{Tr}_{B/K}(xy)=0$ for all $y$ forces $x=0$, and symmetrically. No freeness or reducedness hypothesis on $B$ is imposed; finiteness of $B$ as a $K$-module is the only assumption beyond the algebra structure.
--
--   This is the classical discriminant (trace-form) criterion: a finite algebra over a field is unramified, equivalently étale, precisely when its trace pairing is nondegenerate, the degeneracy being accounted for by nilpotents and by inseparable residue field extensions. It is used here to obtain a pointwise description of unramifiedness over a field in terms of trace duals, in [`Algebra.isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field`](thm.html#Algebra.isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.formallyUnramified_iff_traceForm_nondegenerate_of_finite
    (K : Type u) [Field K] (B : Type u) [CommRing B] [Algebra K B] [Module.Finite K B] :
    Algebra.FormallyUnramified K B ↔ (Algebra.traceForm K B).Nondegenerate := by sorry
