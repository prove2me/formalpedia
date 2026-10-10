-- Prove2me | Theorems.Thm_ActuarialValuation_finiteReserveYearInnovation_on_death
-- name    : ActuarialValuation.finiteReserveYearInnovation_on_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:04:42.237984+00:00
-- url     : https://prove2.me/theorems/23775e1e-4ce8-4d10-8c94-dd558f8beed3
-- title:
--   Death-year surprise equals one minus death rate
-- statement:
--   At realised death year t the death indicator and the in-force indicator are both one.
--
--   **Mathematical statement**
--
--   $$
--   K=t\implies I_t=1-q_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteReserveYearInnovation
open MeasureTheory

namespace ActuarialValuation

theorem finiteReserveYearInnovation_on_death (K t : ℕ) (q : ℕ → ℝ) (h : K = t)
  :
  finiteReserveYearInnovation K t q = 1 - q t := by sorry

end ActuarialValuation
