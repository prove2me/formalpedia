-- Prove2me | Theorems.Thm_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary
-- name    : AlgebraicGeometry.AdmissibleAlgebra.exists_forall_cocycle_pow_smul_eq_coboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/f628de9a-d6ee-51a1-a88d-06d6404cd7e0
-- title:
--   Uniform exponent for t-power torsion in H¹(G,R)
-- statement:
--   Let $B$ be a commutative Noetherian ring, let $R$ be a commutative ring which is a $B$-algebra and finite as a $B$-module, and let $G$ be a finite group acting on $R$ by ring automorphisms in a way compatible with the $B$-action in the sense that the $G$-action and the $B$-action on $R$ commute. Let $t\in B$. The assertion is that there exists an exponent $e\in\mathbb{N}$, depending only on these data and not on the cochain, with the following property: for every map $y\colon G\to R$ satisfying the cocycle identity $y(gh)=g\cdot y(h)+y(g)$ for all $g,h\in G$, if there exist some $k\in\mathbb{N}$ and some $z\in R$ with $t^k\cdot y(g)=g\cdot z-z$ for all $g\in G$, then there exists $z\in R$ with $t^{e}\cdot y(g)=g\cdot z-z$ for all $g\in G$. In cohomological language: the submodule of $t$-power torsion classes in $H^1(G,R)$ is annihilated by the single element $t^{e}$.
--
--   This is the uniform-exponent statement that makes $t$-power torsion in the first group cohomology of a finite module-algebra controllable: a class killed by some power of $t$ is already killed by a power fixed in advance. It is used in [`AlgebraicGeometry.AdmissibleAlgebra.exists_forall_sub_tmul_mem_span_pow_of_flat`](thm.html#AlgebraicGeometry.AdmissibleAlgebra.exists_forall_sub_tmul_mem_span_pow_of_flat), where cocycles arising from a finite group action must be trivialised after multiplication by a bounded power of $t$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u v w

theorem AlgebraicGeometry.AdmissibleAlgebra.exists_forall_cocycle_pow_smul_eq_coboundary
    {B : Type u} [CommRing B] [IsNoetherianRing B] {R : Type v} [CommRing R] [Algebra B R] [Module.Finite B R]
    {G : Type w} [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G B R] (t : B) :
    ∃ e : ℕ, ∀ y : G → R, (∀ g h : G, y (g * h) = g • y h + y g) →
      (∃ (k : ℕ) (z : R), ∀ g : G, t ^ k • y g = g • z - z) → ∃ z : R, ∀ g : G, t ^ e • y g = g • z - z := by sorry
