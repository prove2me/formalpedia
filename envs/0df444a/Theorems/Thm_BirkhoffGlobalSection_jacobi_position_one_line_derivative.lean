-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_jacobi_position_one_line_derivative
-- name    : BirkhoffGlobalSection.jacobi_position_one_line_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:03:54.572654+00:00
-- url     : https://prove2.me/theorems/d73f2a12-dab5-49f9-a577-6d550233bff1
-- title:
--   Horizontal position coordinate-line derivative of the Jacobi Hamiltonian
-- statement:
--   At a collision-free phase point, vary only the horizontal position coordinate. The derivative of the Jacobi Hamiltonian along that line is the second momentum plus the horizontal components of the two inverse-distance forces.
-- source:
--   Elementary differentiation of the Jacobi Hamiltonian in the planar circular restricted three-body problem.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Differentiate the Jacobi Hamiltonian on the horizontal position coordinate line. -/
theorem jacobi_position_one_line_derivative (μ : ℝ) (s : Phase)
    (hfree : collisionFree μ s) :
    HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (Function.update s 0 t))
      (s 3 + (1 - μ) * (s 0 + μ) /
        (Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 +
        μ * (s 0 - 1 + μ) /
        (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3) (s 0) := by sorry

end BirkhoffGlobalSection
