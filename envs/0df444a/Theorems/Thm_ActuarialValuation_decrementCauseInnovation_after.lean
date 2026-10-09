-- Prove2me | Theorems.Thm_ActuarialValuation_decrementCauseInnovation_after
-- name    : ActuarialValuation.decrementCauseInnovation_after
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:03:47.786925+00:00
-- url     : https://prove2.me/theorems/d7ba85dc-3299-4f4b-be47-3d0f71783cf3
-- title:
--   All cause surprises vanish after policy termination
-- statement:
--   Once the insured has left the in-force state, neither another cause-specific termination nor an in-force expected decrement can occur. Both the actual year-and-cause event and the mortality correction indicator vanish in all later years.
--
--   **Mathematical statement**
--
--   $$
--   k<t\Longrightarrow I_{t,c}(k,d)=0
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation

namespace ActuarialValuation

theorem decrementCauseInnovation_after {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t k : ℕ) (c d : C)
  (h : k < t) : decrementCauseInnovation w t c k d = 0 := by sorry

end ActuarialValuation
