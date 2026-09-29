-- Prove2me | Theorems.Thm_FixedPart_exists_smul_eq_zero_forall_of_comp_eq_zero
-- name    : FixedPart.exists_smul_eq_zero_forall_of_comp_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/3f207b9d-9959-56e6-a2a8-13d3b1c220e0
-- title:
--   Common kernel vector with zero annihilator for a square-zero family
-- statement:
--   Let $T$ be a commutative ring that is reduced and Artinian, let $V$ be a $T$-module, and suppose given a $T$-linear isomorphism $e : V \xrightarrow{\sim} T^{2}$, where $T^{2}$ is the module of functions $\mathrm{Fin}\,2 \to T$; thus $V$ is free of rank two. Let $\iota$ be an index type and let $g : \iota \to \operatorname{End}_T(V)$ be a family of $T$-linear endomorphisms of $V$ subject to the single hypothesis that all composites vanish: $g_i \circ g_j = 0$ for all $i, j \in \iota$, the diagonal case $i = j$ included, so each $g_i$ is square-zero and the images of the $g_i$ lie in the intersection of their kernels. The assertion is the existence of a single vector $v \in V$ which is simultaneously annihilated by the whole family, $g_i(v) = 0$ for every $i \in \iota$, and whose annihilator in $T$ is zero, i.e. for every $t \in T$ with $t \cdot v = 0$ one has $t = 0$.
--
--   This is the linear-algebra input to the bound on the fixed part of a rank-two module under a square-zero family of operators: over a reduced Artinian coefficient ring one can find a vector in the common kernel which is not killed by any nonzero scalar. It is cited in the construction of an inertia-fixed vector in a Tate module with a linear independence property over the Hecke lattice algebra, in [`ModularCurve.exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit`](thm.html#ModularCurve.exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FixedPart_exists_smul_eq_zero_forall_of_comp_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Submodule

theorem FixedPart.exists_smul_eq_zero_forall_of_comp_eq_zero
    (T : Type) [CommRing T] [IsReduced T] [IsArtinianRing T]
    (V : Type) [AddCommGroup V] [Module T V] (e : V ≃ₗ[T] (Fin 2 → T))
    {ι : Type} (g : ι → V →ₗ[T] V) (hgg : ∀ i j : ι, g i ∘ₗ g j = 0) :
    ∃ v : V, (∀ i : ι, g i v = 0) ∧ ∀ t : T, t • v = 0 → t = 0 := by sorry
