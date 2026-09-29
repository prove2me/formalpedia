-- Prove2me | Theorems.Thm_Algebra_trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul
-- name    : Algebra.trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/20872429-4cc3-5e30-a699-1be2d118e5b9
-- title:
--   Trace of an elementary tensor in L ⊗_K A
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra that is finite-dimensional over $K$, and let $A$ be a commutative ring that is a $K$-algebra. Form the tensor product $L \otimes_K A$ and regard it as an $A$-algebra via the right-hand factor, i.e. through the algebra structure supplied by the `TensorProduct.RightActions` scoped instances, under which the structure map $A \to L \otimes_K A$ sends $a$ to $1 \otimes a$; this makes $L \otimes_K A$ a finite free $A$-module, so that the $A$-linear trace form is defined on it. The assertion is that for every $l \in L$ and every $a \in A$ the trace of the elementary tensor $l \otimes a$, computed for the $A$-algebra $L \otimes_K A$, equals the image of $\mathrm{Tr}_{L/K}(l)$ under the structure map $K \to A$, multiplied by $a$: $$\mathrm{Tr}_{(L \otimes_K A)/A}(l \otimes_K a) = \mathrm{alg}_{K \to A}\bigl(\mathrm{Tr}_{L/K}(l)\bigr)\, a.$$ Thus the trace form of the base-changed algebra is determined on elementary tensors by the trace form of $L/K$.
--
--   This is the compatibility of the algebra trace with base change, in the elementary-tensor form; it identifies the $A$-valued trace on $L \otimes_K A$ with the $A$-linear extension of $\mathrm{Tr}_{L/K}$. It is used in the archimedean and local volume estimates attached to twisted orbital integrals, where the same trace functional on $L \otimes_K K_v$ occurs in several spellings that must be reconciled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TwistedCommutant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal Topology

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem Algebra.trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] (l : L) (a : A) :
    Algebra.trace A (L ⊗[K] A) (l ⊗ₜ[K] a) = algebraMap K A (Algebra.trace K L l) * a := by sorry
