-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_jacobi_collisionFree_differentiableAt
-- name    : BirkhoffGlobalSection.jacobi_collisionFree_differentiableAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:51:19.093802+00:00
-- url     : https://prove2.me/theorems/de8df7a7-0a3e-48d6-a497-2f98d963bf89
-- title:
--   Differentiability of the Jacobi Hamiltonian away from collisions
-- statement:
--   At every phase point whose position is distinct from both primaries, the Jacobi Hamiltonian is Fréchet differentiable.
-- source:
--   Jacobi Hamiltonian of the planar circular restricted three-body problem, via elementary differential calculus.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The Jacobi Hamiltonian is differentiable away from the two primaries. -/
theorem jacobi_collisionFree_differentiableAt (μ : ℝ) (s : Phase)
    (hfree : collisionFree μ s) :
    DifferentiableAt ℝ (jacobiHamiltonian μ) s := by sorry

end BirkhoffGlobalSection
