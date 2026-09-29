-- Prove2me | Theorems.Thm_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm
-- name    : AutomorphicForm.mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/05eb83ae-7e1d-5323-b5ad-a29d3b119e71
-- title:
--   Cartan double coset membership in GL₂(Kᵥ) via norms
-- statement:
--   Let $K$ be a number field and $v$ a nonzero prime of its ring of integers, with completion $K_v =$ `v.adicCompletion K` carrying its normalised absolute value $\|\cdot\|$, and let $\mathcal{O}_v =$ `v.adicCompletionIntegers K` be the valuation subring. Write $\Gamma_v =$ [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) for the set of $g \in \mathrm{GL}_2(K_v)$ such that both the matrix of $g$ and the matrix of $g^{-1}$ lie in the set of matrices `integralMatrixSet` attached to $\mathcal{O}_v$, i.e. the integrality condition on entries imposed by that subring. Let $\pi \in K_v$ be nonzero with $\|\pi\| \le 1$, let $m_2 \le m_1$ be integers, and let $dl \in \mathrm{GL}_2(K_v)$ be an element whose underlying matrix is $\mathrm{diag}(\pi^{m_1}, \pi^{m_2})$. Then, for $g \in \mathrm{GL}_2(K_v)$, the element $g$ lies in the product set $\Gamma_v \cdot \{dl\} \cdot \Gamma_v$ (pointwise multiplication of subsets) if and only if three conditions hold: $\|\det g\| = \|\pi\|^{m_1+m_2}$; every entry of $g$ satisfies $\|g_{ij}\| \le \|\pi\|^{m_2}$; and some entry satisfies $\|g_{ij}\| = \|\pi\|^{m_2}$. Here the powers are integer powers of the real number $\|\pi\|$. Note that $\pi$ is not required to be a uniformiser.
--
--   This is the local elementary-divisor (Cartan decomposition) criterion for $\mathrm{GL}_2$ over a non-archimedean local field, recast as a numerical test: a double coset of the integral subgroup is pinned down by the norm of the determinant together with the largest norm of an entry. It is used in the estimates for Haar measures of double cosets and for the integral operators acting on automorphic forms, for instance by [`AutomorphicForm.norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det`](thm.html#AutomorphicForm.norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det) and [`AutomorphicForm.exists_uniformizers_forall_exists_cartanType_mem_doubleCoset_and_prod_pow_le_semiLocalHaar`](thm.html#AutomorphicForm.exists_uniformizers_forall_exists_cartanType_mem_doubleCoset_and_prod_pow_le_semiLocalHaar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletion K) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ ≤ 1) (m₁ m₂ : ℤ) (hm : m₂ ≤ m₁)
    (dl : GL (Fin 2) (v.adicCompletion K))
    (hdl : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![π ^ m₁, π ^ m₂])
    (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ AutomorphicForm.localIntegralSet K v * ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
        AutomorphicForm.localIntegralSet K v ↔
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = ‖π‖ ^ (m₁ + m₂) ∧
      (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ ‖π‖ ^ m₂) ∧
      ∃ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ = ‖π‖ ^ m₂ := by sorry
