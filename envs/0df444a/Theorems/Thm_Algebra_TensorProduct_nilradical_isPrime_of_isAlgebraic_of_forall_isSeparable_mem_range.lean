-- Prove2me | Theorems.Thm_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range
-- name    : Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/79136a36-7990-55bf-94e8-7ece670e4c6e
-- title:
--   Primary extensions: L ⊗_K Ω has prime nilradical
-- statement:
--   Let $K$, $L$, $\Omega$ be fields with $L$ and $\Omega$ both $K$-algebras, and assume $\Omega$ is algebraic over $K$. Assume further that $K$ is separably closed in $L$, in the sense that every $y \in L$ which is separable over $K$ (the predicate `IsSeparable K y`) lies in the image of the structure map $K \to L$. The conclusion is that the nilradical of the $K$-algebra $L \otimes_K \Omega$, i.e. the ideal of nilpotent elements, is a prime ideal: it is not the whole ring, and whenever a product $ab$ in $L \otimes_K \Omega$ is nilpotent, $a$ or $b$ is nilpotent. Equivalently, $\operatorname{Spec}(L \otimes_K \Omega)$ is irreducible. Nothing is asserted about $L \otimes_K \Omega$ being reduced, and $\Omega$ is not assumed separable, normal or algebraically closed, only algebraic over $K$.
--
--   This is one implication of the classical characterisation of primary (geometrically irreducible) field extensions: if $K$ is separably closed in $L$ then $L \otimes_K \Omega$ has irreducible spectrum for every algebraic extension $\Omega/K$. It is used in the proof that a separable polynomial over such an $L$ remains irreducible after base change to an algebraic closure, in [`Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range`](thm.html#Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range
    (K : Type u) (L : Type v) (Ω : Type w) [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (hsc : ∀ y : L, IsSeparable K y → y ∈ (algebraMap K L).range) :
    (nilradical (L ⊗[K] Ω)).IsPrime := by sorry
