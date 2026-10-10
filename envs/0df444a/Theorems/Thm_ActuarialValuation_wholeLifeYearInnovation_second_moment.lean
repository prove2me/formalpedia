-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_second_moment
-- name    : ActuarialValuation.wholeLifeYearInnovation_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:10:12.436731+00:00
-- url     : https://prove2.me/theorems/001fdbd9-f670-46da-a968-0d007f03bdba
-- title:
--   Yearly innovation variance includes subsequent survival probability
-- statement:
--   Year-t mortality surprise is one minus mortality probability on actual deaths, minus mortality probability on later deaths, and zero on earlier deaths. The resulting weighted second moment is death mass multiplied by the conditional probability of surviving that year.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[I_t^2]=w_t S_{t+1}/S_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeYearInnovation_second_moment (w : ℕ → ℝ) (t : ℕ)
  (hw : Summable w) (hS : 0 < wholeLifeTailMass w t) :
  (∑' k : ℕ, w k * (wholeLifeYearInnovation w t k) ^ 2) =
    w t * (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t) := by sorry

end ActuarialValuation
