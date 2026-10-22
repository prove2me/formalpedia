-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_one
-- name    : BirkhoffGlobalSection.jacobi_partial_position_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:42:45.5374+00:00
-- url     : https://prove2.me/theorems/a66ea050-1184-42f7-894c-faecc02dd6a7
-- title:
--   Horizontal position derivative of the Jacobi Hamiltonian
-- statement:
--   At a collision-free phase point, the derivative of the rotating-frame Jacobi Hamiltonian in the first position coordinate is the second momentum plus the two horizontal gravitational inverse-cube contributions. Each squared primary distance is positive, so the displayed real square-root denominators are nonzero.
-- source:
--   Direct differentiation of Joung--van Koert Jacobi Hamiltonian, equation (1.1), https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Horizontal position derivative of the Jacobi Hamiltonian away from both
collisions. -/
theorem jacobi_partial_position_one (μ : ℝ) (s : Phase)
    (hfree : collisionFree μ s) :
    partialDerivative (jacobiHamiltonian μ) s 0 =
      s 3 + (1 - μ) * (s 0 + μ) /
        (Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 +
      μ * (s 0 - 1 + μ) /
        (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 := by sorry

end BirkhoffGlobalSection
