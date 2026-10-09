-- Prove2me | Theorems.Thm_ActuarialValuation_finiteReserveLossAtIssue_zero
-- name    : ActuarialValuation.finiteReserveLossAtIssue_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T08:59:09.744867+00:00
-- url     : https://prove2.me/theorems/fd509c2c-bc93-455d-925a-8fd2474eb678
-- title:
--   Zero-horizon loss is exactly the opening reserve
-- statement:
--   With no covered years, the premium and death-benefit sums are empty, and all that remains is the current reserve.
--
--   **Mathematical statement**
--
--   $$
--   L_0=V_0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteReserveLossAtIssue
open MeasureTheory

namespace ActuarialValuation

theorem finiteReserveLossAtIssue_zero (K : ℕ) (v : ℝ) (premium benefit reserve : ℕ → ℝ)
  :
  finiteReserveLossAtIssue K 0 v premium benefit reserve = reserve 0 := by sorry

end ActuarialValuation
