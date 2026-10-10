-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeFiniteInnovation_zero
-- name    : ActuarialValuation.wholeLifeFiniteInnovation_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:08:02.223093+00:00
-- url     : https://prove2.me/theorems/904efc57-8a77-403d-8b0d-2c01e7329dd5
-- title:
--   The zero-horizon centred loss is zero
-- statement:
--   No policy year enters the finite range at horizon zero. The discounted sum of mortality surprises is therefore empty and evaluates to zero, regardless of the benefit, premium or survival assumptions.
--
--   **Mathematical statement**
--
--   $$
--   Z_0(k)=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeFiniteInnovation

namespace ActuarialValuation

theorem wholeLifeFiniteInnovation_zero (w rho : ℕ → ℝ) (k : ℕ) :
  wholeLifeFiniteInnovation w rho 0 k = 0 := by sorry

end ActuarialValuation
