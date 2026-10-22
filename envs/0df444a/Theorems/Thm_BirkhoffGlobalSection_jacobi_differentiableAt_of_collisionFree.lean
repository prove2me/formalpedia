-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_jacobi_differentiableAt_of_collisionFree
-- name    : BirkhoffGlobalSection.jacobi_differentiableAt_of_collisionFree
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:06:16.324118+00:00
-- url     : https://prove2.me/theorems/1368e33c-ab6e-409a-b29c-4b6b117d8aa6
-- title:
--   Differentiability of the Jacobi Hamiltonian off collisions
-- statement:
--   For every real mass parameter $\mu$ and every phase point $s\in\mathbb R^4$ away from both primary collisions, the Jacobi Hamiltonian $H_\mu$ is Fréchet differentiable at $s$.
--
--   $$
--   \operatorname{collisionFree}(\mu,s)\Longrightarrow H_\mu\text{ is differentiable at }s.
--   $$
--
--   This analytic foundation prevents totalized derivatives at singular points from being mistaken for genuine critical points.
-- source:
--   Joung--van Koert, equation (1.1), https://arxiv.org/abs/2407.19159v3. Differentiability off the two displayed collision denominators is the analytic consequence formalized here.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The Jacobi Hamiltonian is differentiable away from the two collision
positions. -/
theorem jacobi_differentiableAt_of_collisionFree (μ : ℝ) (s : Phase)
    (hs : collisionFree μ s) :
    DifferentiableAt ℝ (jacobiHamiltonian μ) s := by sorry

end BirkhoffGlobalSection
