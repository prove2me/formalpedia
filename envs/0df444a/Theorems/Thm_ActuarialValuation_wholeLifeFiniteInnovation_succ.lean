-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeFiniteInnovation_succ
-- name    : ActuarialValuation.wholeLifeFiniteInnovation_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:08:35.130248+00:00
-- url     : https://prove2.me/theorems/f4701a07-64d9-4788-86a4-87619b7a710a
-- title:
--   An additional year adds its own discounted mortality shock
-- statement:
--   A successor horizon appends exactly one new year to the finite innovation sum. Its contribution is the current year's discounted net amount at risk multiplied by the death-year innovation, preserving the precise timing of year-end benefit payments.
--
--   **Mathematical statement**
--
--   $$
--   Z_{n+1}(k)=Z_n(k)+\rho_nI_n(k)
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeFiniteInnovation
import Definitions.Def_actuarial_wholeLifeYearInnovation

namespace ActuarialValuation

theorem wholeLifeFiniteInnovation_succ (w rho : ℕ → ℝ) (n k : ℕ) :
  wholeLifeFiniteInnovation w rho (n + 1) k =
    wholeLifeFiniteInnovation w rho n k +
      rho n * wholeLifeYearInnovation w n k := by sorry

end ActuarialValuation
