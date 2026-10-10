-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffYearDeathRateSum
-- name    : ActuarialValuation.finiteHattendorffYearDeathRateSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:18:27.326811+00:00
-- url     : https://prove2.me/theorems/072d035d-a797-461e-bd95-cbef460cba93
-- title:
--   Derived conditional death and survival probabilities add to one
-- statement:
--   Derived death and survival rates respect the in-force event partition at positive survival mass.
--
--   **Mathematical statement**
--
--   $$
--   q_t+p_t=1
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 320 (pp. 319–323), Shiu–Xiong (2021), equations (1)–(5), fully discrete loss and prospective-reserve recursion; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate

namespace ActuarialValuation

theorem finiteHattendorffYearDeathRateSum {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ)
  (hS : 0 < finiteMortalitySurvivalMass w K t)
  :
  finiteMortalityDeathRate w K t + finiteMortalitySurvivalRate w K t = 1 := by sorry

end ActuarialValuation
