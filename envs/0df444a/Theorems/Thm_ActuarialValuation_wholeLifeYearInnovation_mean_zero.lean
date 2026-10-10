-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_mean_zero
-- name    : ActuarialValuation.wholeLifeYearInnovation_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:09:30.522557+00:00
-- url     : https://prove2.me/theorems/c6c9fa40-f348-4227-a78d-e96442b4c1bf
-- title:
--   Year-specific mortality innovation is centred
-- statement:
--   The weighted observed-year death indicator has mean w(t). The expected in-force correction is w(t) divided by survival mass times that same survival mass. Countable summability and positive survival ensure the two contributions cancel exactly.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[I_t]=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeYearInnovation_mean_zero (w : ℕ → ℝ) (t : ℕ)
  (hw : Summable w) (hS : 0 < wholeLifeTailMass w t) :
  (∑' k : ℕ, w k * wholeLifeYearInnovation w t k) = 0 := by sorry

end ActuarialValuation
