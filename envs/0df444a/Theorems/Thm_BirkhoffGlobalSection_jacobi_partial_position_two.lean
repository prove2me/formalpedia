-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_two
-- name    : BirkhoffGlobalSection.jacobi_partial_position_two
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:42:40.103617+00:00
-- url     : https://prove2.me/theorems/d0d1f43c-2ece-4360-ad84-4539f64aa2e9
-- title:
--   Vertical position derivative of the Jacobi Hamiltonian
-- statement:
--   At a collision-free phase point, the derivative of the rotating-frame Jacobi Hamiltonian in the second position coordinate is minus the first momentum plus the two vertical gravitational inverse-cube contributions. The formula uses both positive primary distances.
-- source:
--   Direct differentiation of Joung--van Koert Jacobi Hamiltonian, equation (1.1), https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Vertical position derivative of the Jacobi Hamiltonian away from both
collisions. -/
theorem jacobi_partial_position_two (μ : ℝ) (s : Phase)
    (hfree : collisionFree μ s) :
    partialDerivative (jacobiHamiltonian μ) s 1 =
      -s 2 + (1 - μ) * (s 1) /
        (Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 +
      μ * (s 1) /
        (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 := by sorry

end BirkhoffGlobalSection
