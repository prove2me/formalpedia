-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_after
-- name    : ActuarialValuation.wholeLifeYearInnovation_after
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:05:39.434966+00:00
-- url     : https://prove2.me/theorems/319c0985-06a2-4504-8e00-71fde600464e
-- title:
--   Mortality innovation vanishes strictly after death
-- statement:
--   After the death year, the observed death-in-year indicator and the start-of-year in-force indicator are both zero. The centred annual mortality surprise is consequently zero for all later years, without a global upper age bound.
--
--   **Mathematical statement**
--
--   $$
--   k<t\Longrightarrow I_t(k)=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation

namespace ActuarialValuation

theorem wholeLifeYearInnovation_after (w : ℕ → ℝ) (t k : ℕ)
  (h : k < t) : wholeLifeYearInnovation w t k = 0 := by sorry

end ActuarialValuation
