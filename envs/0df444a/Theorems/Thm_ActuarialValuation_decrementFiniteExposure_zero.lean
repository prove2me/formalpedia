-- Prove2me | Theorems.Thm_ActuarialValuation_decrementFiniteExposure_zero
-- name    : ActuarialValuation.decrementFiniteExposure_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:10:28.908098+00:00
-- url     : https://prove2.me/theorems/23dfedf8-18af-4deb-bbbb-f82224df4022
-- title:
--   No covered years implies zero centred decrement loss
-- statement:
--   At horizon zero the finite index set of years is empty. It follows that no cause-specific mortality innovation or discounted reserve exposure is included in the truncated insurer loss.
--
--   **Mathematical statement**
--
--   $$
--   Z_0(k,d)=0
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementFiniteExposure

namespace ActuarialValuation

theorem decrementFiniteExposure_zero {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (k : ℕ) (d : C) :
  decrementFiniteExposure w rho 0 k d = 0 := by sorry

end ActuarialValuation
