-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_survivor
-- name    : ActuarialValuation.wholeLifeYearInnovation_survivor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:07:20.449786+00:00
-- url     : https://prove2.me/theorems/962de78f-4538-4222-8498-5d6e04941bd8
-- title:
--   Surviving the year produces a negative conditional surprise
-- statement:
--   For a death occurring after year t, the insured is still in force at that year but no death occurs then. Subtracting conditional mortality from a zero observed death yields minus that year's conditional death probability.
--
--   **Mathematical statement**
--
--   $$
--   t<k\Longrightarrow I_t(k)=-q_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeYearInnovation_survivor (w : ℕ → ℝ) (t k : ℕ)
  (h : t < k) :
  wholeLifeYearInnovation w t k =
    -(w t / wholeLifeTailMass w t) := by sorry

end ActuarialValuation
