-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_jacobi_momentum_two_line_derivative
-- name    : BirkhoffGlobalSection.jacobi_momentum_two_line_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:17:19.106982+00:00
-- url     : https://prove2.me/theorems/0f1b833f-7d06-43c8-b208-e754be5f5f71
-- title:
--   Derivative along the second Jacobi momentum coordinate
-- statement:
--   Fix any phase point and vary only its second momentum coordinate $p_2$. The rotating-frame Jacobi Hamiltonian has ordinary derivative $p_2+q_1$ at that point. The gravitational terms remain constant along this line, including at positions where their totalized expressions are singular.
-- source:
--   For the Hamiltonian calculation: Joung--van Koert, equation (1.1), https://arxiv.org/abs/2407.19159v3. The derivative bridge is the standard chain rule for an affine coordinate line.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Along the second momentum coordinate line, the potential is constant and
the Jacobi Hamiltonian is quadratic in that coordinate. -/
theorem jacobi_momentum_two_line_derivative (μ : ℝ) (s : Phase) :
    HasDerivAt
      (fun t : ℝ => jacobiHamiltonian μ (Function.update s (3 : Fin 4) t))
      (s 3 + s 0) (s 3) := by sorry

end BirkhoffGlobalSection
