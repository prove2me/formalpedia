-- Prove2me | Theorems.Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range
-- name    : Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/5a2969df-ebf6-541e-8e93-939c422e2678
-- title:
--   Primary extensions are linearly disjoint from separable ones
-- statement:
--   Let $k$, $F$, $K$ be fields with $F$ and $K$ both $k$-algebras, and suppose $K$ is separable over $k$ in Mathlib's sense: every element of $K$ is algebraic over $k$ with separable minimal polynomial. Suppose further that $k$ is separably algebraically closed in $F$, in the form of the hypothesis `hsc`: every $y \in F$ whose minimal polynomial over $k$ is separable (in particular, every such $y$ is algebraic over $k$) lies in the image of the structure map $k \to F$. The conclusion is that the commutative ring $F \otimes_k K$ satisfies `IsField`, i.e. it has two distinct elements, its multiplication is commutative, and every nonzero element has a multiplicative inverse. Note that the assertion is about the ring structure on the tensor product only; no field instance is produced, and $F/k$ is not assumed algebraic or finitely generated.
--
--   This is the standard linear disjointness statement that a primary extension $F/k$ — one in which $k$ is separably algebraically closed — is linearly disjoint from every separable algebraic extension $K/k$, so that $F \otimes_k K$ is again a field; equivalently, $F/k$ is geometrically irreducible as far as separable base changes are concerned. It is used in [`Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range`](thm.html#Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range), where the separable part of an algebraic base change is split off from the purely inseparable part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range
    (k : Type u) (F : Type v) (K : Type w) [Field k] [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra.IsSeparable k K]
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range) :
    IsField (F ⊗[k] K) := by sorry
