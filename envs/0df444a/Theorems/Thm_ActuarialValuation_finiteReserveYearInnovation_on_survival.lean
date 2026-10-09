-- Prove2me | Theorems.Thm_ActuarialValuation_finiteReserveYearInnovation_on_survival
-- name    : ActuarialValuation.finiteReserveYearInnovation_on_survival
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:01:14.330495+00:00
-- url     : https://prove2.me/theorems/3dd4ef63-c61a-4038-b2e6-67b1313def40
-- title:
--   Surviving a year produces negative death surprise
-- statement:
--   On strictly later death year K>t, death-in-year indicator is zero but the in-force indicator equals one.
--
--   **Mathematical statement**
--
--   $$
--   K>t\implies I_t=-q_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteReserveYearInnovation
open MeasureTheory

namespace ActuarialValuation

theorem finiteReserveYearInnovation_on_survival (K t : ℕ) (q : ℕ → ℝ) (h : t < K)
  :
  finiteReserveYearInnovation K t q = -q t := by sorry

end ActuarialValuation
