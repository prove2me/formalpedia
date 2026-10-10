-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffCoefficient_identity
-- name    : ActuarialValuation.finiteHattendorffCoefficient_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:19:03.491231+00:00
-- url     : https://prove2.me/theorems/bc557092-e3cc-487a-aff8-04061eca99fa
-- title:
--   Net amount at risk coefficient is deterministic and discounted
-- statement:
--   The annual discounted risk coefficient has the same timing as the reserve-loss bridge.
--
--   **Mathematical statement**
--
--   $$
--   \rho_t=v^{t+1}(b_{t+1}-V_{t+1})
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 320 (pp. 319–323), Shiu–Xiong (2021), equations (1)–(5), fully discrete loss and prospective-reserve recursion; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk

namespace ActuarialValuation

theorem finiteHattendorffCoefficient_identity (v : ℝ) (benefit reserve : ℕ → ℝ) (t : ℕ)
  :
  finiteHattendorffNetAtRisk v benefit reserve t =
  v ^ (t + 1) * (benefit (t + 1) - reserve (t + 1)) := by sorry

end ActuarialValuation
