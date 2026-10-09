-- Prove2me | Theorems.Thm_ActuarialValuation_decrementYearMass_nonneg
-- name    : ActuarialValuation.decrementYearMass_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:02:51.848352+00:00
-- url     : https://prove2.me/theorems/e76bb1fe-fd5a-4bfb-b08a-f89331ef58c0
-- title:
--   Nonnegative cause masses yield a nonnegative annual death mass
-- statement:
--   All cause incidence masses are nonnegative by assumption. Adding finitely many such masses gives a nonnegative aggregate termination probability in the year, including the possibility that every cause has probability zero.
--
--   **Mathematical statement**
--
--   $$
--   D_t\ge0
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementYearMass

namespace ActuarialValuation

theorem decrementYearMass_nonneg {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) (hw : ∀ c, 0 ≤ w t c) :
  0 ≤ decrementYearMass w t := by sorry

end ActuarialValuation
