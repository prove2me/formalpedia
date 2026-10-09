-- Prove2me | Theorems.Thm_ActuarialValuation_decrementFiniteExposure_succ
-- name    : ActuarialValuation.decrementFiniteExposure_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:11:11.547207+00:00
-- url     : https://prove2.me/theorems/b8df1b0d-ef0c-4b93-ac54-37ee10e86e1c
-- title:
--   An extra year adds all of its cause-specific mortality shocks
-- statement:
--   The successor-year reserve innovation equals its predecessor plus one complete cause sum at the newly included year. Mutually exclusive causes must be combined within the year rather than treated as independent chronological increments.
--
--   **Mathematical statement**
--
--   $$
--   Z_{n+1}(k,d)=Z_n(k,d)+\sum_c\rho_{n,c}I_{n,c}
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementFiniteExposure
import Definitions.Def_actuarial_decrementCauseInnovation

namespace ActuarialValuation

theorem decrementFiniteExposure_succ {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (n k : ℕ) (d : C) :
  decrementFiniteExposure w rho (n + 1) k d =
    decrementFiniteExposure w rho n k d +
      ∑ c : C, rho n c * decrementCauseInnovation w n c k d := by sorry

end ActuarialValuation
