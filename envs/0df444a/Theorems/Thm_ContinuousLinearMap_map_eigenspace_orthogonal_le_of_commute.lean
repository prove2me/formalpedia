-- Prove2me | Theorems.Thm_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute
-- name    : ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/3c0cc7a6-4256-517e-a85f-7d897d3266e3
-- title:
--   Commuting operators preserve eigenspaces of a symmetric operator
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ (an `RCLike` field) and let $E$ be a complete inner product space over $\mathbb{K}$. Let $T : E \to E$ be a continuous linear map which is a compact operator and whose underlying linear map is symmetric, i.e. $\langle T x, y\rangle = \langle x, T y\rangle$ for all $x, y$. Let $S : E \to E$ be a continuous linear map commuting with $T$ in the sense that the composite $T$ followed by $S$ equals the composite $S$ followed by $T$, and let $\mu \in \mathbb{K}$ be nonzero. Writing $E_\mu = \ker(T - \mu)$ for the $\mu$-eigenspace of $T$ viewed as an endomorphism of $E$, the conclusion is the conjunction of two inclusions of submodules: the image of $E_\mu$ under $S$ is contained in $E_\mu$, and the image of the orthogonal complement $E_\mu^{\perp}$ under $S$ is contained in $E_\mu^{\perp}$.
--
--   This is the standard statement that a bounded operator commuting with a bounded symmetric operator reduces each eigenspace of the latter and its orthogonal complement. It is used in the spectral analysis of the cuspidal spectrum for $GL(2)$, where it guarantees that an operator acting by a scalar on a vector continues to act by that scalar on the vector's spectral components: it is cited by [`AutomorphicForm.CuspidalSpectrum.exists_slice_sub_mem_eigenspace_orthogonal`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_slice_sub_mem_eigenspace_orthogonal) and [`AutomorphicForm.CuspidalSpectrum.exists_slice_sub_mem_eigenspace_orthogonal_principal`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_slice_sub_mem_eigenspace_orthogonal_principal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Module.End
open scoped InnerProductSpace

theorem ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
    (S : E →L[𝕜] E) (hST : S.comp T = T.comp S) (μ : 𝕜) (hμ : μ ≠ 0) :
    (eigenspace (T : Module.End 𝕜 E) μ).map (S : Module.End 𝕜 E) ≤ eigenspace (T : Module.End 𝕜 E) μ ∧
    ((eigenspace (T : Module.End 𝕜 E) μ)ᗮ).map (S : Module.End 𝕜 E) ≤ (eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by sorry
