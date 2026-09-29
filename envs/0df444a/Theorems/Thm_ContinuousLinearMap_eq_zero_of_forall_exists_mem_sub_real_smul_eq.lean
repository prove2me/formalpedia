-- Prove2me | Theorems.Thm_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq
-- name    : ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/8e1a6be7-a586-55aa-8bd1-f783a21ebe36
-- title:
--   Symmetry on a subspace forbids v∈(T-c)(E) for all real c
-- statement:
--   Let $H$ be a complex Hilbert space (a normed additive commutative group with a complex inner product structure, assumed complete), let $T \colon H \to H$ be a continuous $\mathbb{C}$-linear map, and let $E$ be a $\mathbb{C}$-submodule of $H$ — no closedness of $E$ and no $T$-stability of $E$ is assumed. Suppose $T$ is symmetric on $E$ in the sense that $\langle T x, y\rangle = \langle x, T y\rangle$ for all $x, y \in E$, the inner product being the complex-valued one. Let $v \in H$ be a vector such that for every real number $c$ there exists $w \in E$ with $T w - c\,w = v$, where the real scalar $c$ acts through its image in $\mathbb{C}$. The conclusion is that $v = 0$. Equivalently, the only vector of $H$ lying simultaneously in all the sets $(T - c)(E)$, as $c$ ranges over $\mathbb{R}$, is the zero vector.
--
--   This is a Schur-type rigidity statement for a bounded operator that is merely symmetric on a subspace: it requires neither compactness of $T$, nor the existence of an eigenvector, nor completeness of $E$. It is used in the analysis of cuspidal constituents of automorphic forms, where it yields that a spherical Hecke-type operator acting on a subspace must act by a real scalar, in [`AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType`](thm.html#AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType) and its principal-series counterpart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped InnerProductSpace

theorem ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (E : Submodule ℂ H)
    (hsym : ∀ x ∈ E, ∀ y ∈ E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (v : H) (hsurj : ∀ c : ℝ, ∃ w ∈ E, T w - (c : ℂ) • w = v) :
    v = 0 := by sorry
