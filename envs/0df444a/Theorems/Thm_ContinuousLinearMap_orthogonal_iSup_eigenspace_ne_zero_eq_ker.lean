-- Prove2me | Theorems.Thm_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker
-- name    : ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/9b157d55-6fac-50a1-a424-4b346c1ec0da
-- title:
--   Orthogonal complement of the non-zero eigenspaces is ker T
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ (an `RCLike` field) and let $E$ be a $\mathbb{K}$-inner product space whose underlying normed additive group is complete, so a Hilbert space. Let $T \colon E \to E$ be a continuous $\mathbb{K}$-linear map, and assume two hypotheses: that $T$ is a compact operator, i.e. some neighbourhood of $0$ in $E$ has relatively compact image under $T$, and that the underlying $\mathbb{K}$-linear map of $T$ is symmetric, i.e. $\langle T x, y\rangle = \langle x, T y\rangle$ for all $x, y \in E$. The conclusion is an equality of submodules of $E$: the orthogonal complement of $\bigsqcup_{\mu \neq 0} \ker(T - \mu\,\mathrm{id})$, the supremum in the lattice of submodules (equivalently, the span of the union) of the eigenspaces of $T$ at all non-zero scalars $\mu \in \mathbb{K}$, coincides with the kernel of $T$. In particular no closure is taken before forming the orthogonal complement, and the eigenspaces are indexed by all non-zero $\mu$, most of which contribute $0$.
--
--   This is the part of the spectral theorem for compact self-adjoint operators (Hilbert–Schmidt theorem) asserting that the eigenspaces at non-zero eigenvalues together with $\ker T$ exhaust the space: a vector orthogonal to all of them is killed by $T$. It is used in the analytic step that extracts eigenvectors of smoothing (right convolution) operators on spaces of automorphic forms, where it identifies the vectors on which such an operator vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Module.End

theorem ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E) := by sorry
