-- Prove2me | Theorems.Thm_ActuarialValuation_finiteReserveLossAtIssue_succ
-- name    : ActuarialValuation.finiteReserveLossAtIssue_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:08:12.162681+00:00
-- url     : https://prove2.me/theorems/d466be4f-1925-4111-93b0-da0306aee559
-- title:
--   Loss with one further policy year
-- statement:
--   The longer-horizon insurer loss adjusts for one more year's claim and premium, replacing the former terminal reserve with the new one.
--
--   **Mathematical statement**
--
--   $$
--   L_{n+1}-L_n=v^{n+1}bD_n-v^n\pi_nS_n+v^{n+1}V_{n+1}S_{n+1}-v^nV_nS_n
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
import Definitions.Def_actuarial_finiteLifeInForceIndicator
import Definitions.Def_actuarial_finiteReserveLossAtIssue
open MeasureTheory

namespace ActuarialValuation

theorem finiteReserveLossAtIssue_succ (K n : ℕ) (v : ℝ) (premium benefit reserve : ℕ → ℝ)
  :
  finiteReserveLossAtIssue K (n + 1) v premium benefit reserve =
  finiteReserveLossAtIssue K n v premium benefit reserve +
  v ^ (n + 1) * benefit (n + 1) * finiteLifeDeathIndicator K n -
  v ^ n * premium n * finiteLifeInForceIndicator K n +
  v ^ (n + 1) * reserve (n + 1) * finiteLifeInForceIndicator K (n + 1) -
  v ^ n * reserve n * finiteLifeInForceIndicator K n := by sorry

end ActuarialValuation
