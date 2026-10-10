-- Prove2me | Theorems.Thm_ActuarialValuation_finiteReserveYearInnovation_after_death
-- name    : ActuarialValuation.finiteReserveYearInnovation_after_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T08:59:45.449979+00:00
-- url     : https://prove2.me/theorems/683d491e-bc76-435d-a27b-c11078fd1fea
-- title:
--   Annual surprise is zero after death
-- statement:
--   Neither death in year t nor survival to its start is possible after the policy has ended.
--
--   **Mathematical statement**
--
--   $$
--   K<t\implies I_t=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteReserveYearInnovation
open MeasureTheory

namespace ActuarialValuation

theorem finiteReserveYearInnovation_after_death (K t : ℕ) (q : ℕ → ℝ) (h : K < t)
  :
  finiteReserveYearInnovation K t q = 0 := by sorry

end ActuarialValuation
