-- Prove2me | Theorems.Thm_ActuarialValuation_finiteLifeInForce_partition
-- name    : ActuarialValuation.finiteLifeInForce_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T08:58:31.926238+00:00
-- url     : https://prove2.me/theorems/045da584-2d37-41d6-95df-e814d7a1e3a2
-- title:
--   Year-start survival splits into death and later survival
-- statement:
--   The in-force event at time t is the disjoint sum of death in year t and still being in force at t+1.
--
--   **Mathematical statement**
--
--   $$
--   S_t=D_t+S_{t+1}
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
import Definitions.Def_actuarial_finiteLifeInForceIndicator
open MeasureTheory

namespace ActuarialValuation

theorem finiteLifeInForce_partition (K t : ℕ)
  :
  finiteLifeInForceIndicator K t = finiteLifeDeathIndicator K t + finiteLifeInForceIndicator K (t + 1) := by sorry

end ActuarialValuation
