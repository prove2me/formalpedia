-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_at
-- name    : ActuarialValuation.wholeLifeYearInnovation_at
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:06:43.964206+00:00
-- url     : https://prove2.me/theorems/7c9aaf23-18e4-42cc-8e0d-f1e6b56ef5cc
-- title:
--   Observed-death innovation equals one minus conditional mortality
-- statement:
--   When the realised decrement year is precisely t, both observed death and in-force indicators equal one. The surprise is therefore one less the year-t death probability conditional on having survived to that year.
--
--   **Mathematical statement**
--
--   $$
--   I_t(t)=1-q_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeYearInnovation_at (w : ℕ → ℝ) (t : ℕ) :
  wholeLifeYearInnovation w t t =
    1 - w t / wholeLifeTailMass w t := by sorry

end ActuarialValuation
