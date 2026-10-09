-- Prove2me | Theorems.Thm_ActuarialValuation_finiteLifeDeathIndicator_after_death
-- name    : ActuarialValuation.finiteLifeDeathIndicator_after_death
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T08:58:00.122223+00:00
-- url     : https://prove2.me/theorems/64a30a48-679a-476a-a0b3-034adb8ca15d
-- title:
--   No death-year event after actual death
-- statement:
--   The death-year indicator for later years is zero.
--
--   **Mathematical statement**
--
--   $$
--   t>K\implies D_t(K)=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
open MeasureTheory

namespace ActuarialValuation

theorem finiteLifeDeathIndicator_after_death (K t : ℕ) (h : K < t)
  :
  finiteLifeDeathIndicator K t = 0 := by sorry

end ActuarialValuation
