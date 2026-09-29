-- Prove2me | Theorems.Thm_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat
-- name    : AlgebraicGeometry.AdmissibleAlgebra.forall_pow_smul_mem_range_rTensor_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/bf2a0294-c32b-5d62-9b39-b7bf67036cae
-- title:
--   Bounded t-power torsion in homology survives flat base change
-- statement:
--   Let $B$ be a commutative ring and let $M, N, P$ be $B$-modules, all three in a single universe, together with $B$-linear maps $f : M \to N$ and $g : N \to P$ satisfying $g \circ f = 0$. Fix $t \in B$ and $e \in \mathbb{N}$, and assume that every $n \in N$ with $g(n) = 0$ for which $t^k n$ lies in the image of $f$ for some $k \in \mathbb{N}$ already satisfies $t^e n \in \operatorname{im} f$; that is, the $t$-power torsion of $\ker g / \operatorname{im} f$ is annihilated by $t^e$. Let $S$ be a flat $B$-module in the same universe as $M, N, P$. The conclusion is that the analogous statement holds after tensoring on the right by $S$: for every $n \in N \otimes_B S$ with $(g \otimes 1)(n) = 0$, if $t^k n$ lies in the range of $f \otimes 1 : M \otimes_B S \to N \otimes_B S$ for some $k \in \mathbb{N}$, then $t^e n$ lies in the range of $f \otimes 1$, with the same exponent $e$. Base change is expressed throughout by `LinearMap.rTensor`.
--
--   This is a piece of homological algebra about flat base change of a three-term complex: uniform annihilation of the $t$-power torsion of its homology is preserved, with no change of exponent and with no Noetherian hypothesis on $B$. It is used by [`AlgebraicGeometry.AdmissibleAlgebra.exists_forall_sub_tmul_mem_span_pow_of_flat`](thm.html#AlgebraicGeometry.AdmissibleAlgebra.exists_forall_sub_tmul_mem_span_pow_of_flat) in the descent-type arguments about admissible algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u v w

theorem AlgebraicGeometry.AdmissibleAlgebra.forall_pow_smul_mem_range_rTensor_of_flat
    {B : Type u} [CommRing B] {M N P : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (f : M →ₗ[B] N) (g : N →ₗ[B] P) (hfg : g.comp f = 0) (t : B) (e : ℕ)
    (h : ∀ n : N, g n = 0 → (∃ k : ℕ, t ^ k • n ∈ LinearMap.range f) → t ^ e • n ∈ LinearMap.range f)
    (S : Type v) [AddCommGroup S] [Module B S] [Module.Flat B S]
    (n : N ⊗[B] S) (hn : LinearMap.rTensor S g n = 0) (hk : ∃ k : ℕ, t ^ k • n ∈ LinearMap.range (LinearMap.rTensor S f)) :
    t ^ e • n ∈ LinearMap.range (LinearMap.rTensor S f) := by sorry
