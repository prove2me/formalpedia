-- Prove2me | Theorems.Thm_ActuarialValuation_decrementAnnualRisk_scale
-- name    : ActuarialValuation.decrementAnnualRisk_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:13:26.229007+00:00
-- url     : https://prove2.me/theorems/fb4802e7-c27b-4984-8450-67d9f106ac1b
-- title:
--   Uniformly scaling cause exposures scales variance quadratically
-- statement:
--   Multiplying all discounted death-benefit net amounts at risk by a common currency factor scales both the second-moment term and the squared-mean correction by its square. The annual allocation therefore obeys the standard quadratic scaling law.
--
--   **Mathematical statement**
--
--   $$
--   A_t(a\rho)=a^2A_t(\rho)
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementAnnualRisk

namespace ActuarialValuation

theorem decrementAnnualRisk_scale {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (a : ℝ) (t : ℕ) :
  decrementAnnualRisk w (fun n c => a * rho n c) t =
    a ^ 2 * decrementAnnualRisk w rho t := by sorry

end ActuarialValuation
