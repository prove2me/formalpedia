-- Prove2me | Theorems.Thm_ActuarialValuation_decrementAnnualRisk_zero_exposure
-- name    : ActuarialValuation.decrementAnnualRisk_zero_exposure
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:11:51.731485+00:00
-- url     : https://prove2.me/theorems/95dd5cec-1c03-49ab-b3af-73bb9ca910ef
-- title:
--   Zero net amounts at risk imply zero annual mortality variance
-- statement:
--   If every named cause carries zero discounted net amount at risk, both the sum of squared exposures and the squared conditional-mean correction vanish, so there is no mortality risk allocation in that year.
--
--   **Mathematical statement**
--
--   $$
--   \rho_{t,c}=0\ \forall c\Longrightarrow A_t=0
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementAnnualRisk

namespace ActuarialValuation

theorem decrementAnnualRisk_zero_exposure {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) :
  decrementAnnualRisk w (fun _ _ => 0) t = 0 := by sorry

end ActuarialValuation
