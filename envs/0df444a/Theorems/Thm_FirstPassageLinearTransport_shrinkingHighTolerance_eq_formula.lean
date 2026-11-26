-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingHighTolerance_eq_formula
-- name    : FirstPassageLinearTransport.shrinkingHighTolerance_eq_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:34.784662+00:00
-- url     : https://prove2.me/theorems/7e71460f-d967-56cb-b255-9e7c2fbee6c3
-- title:
--   First Passage Linear Transport: shrinking High Tolerance eq formula
-- statement:
--   The high tolerance cap is inactive whenever the current rank dominates
--   `C log (M+2)` and `D / sqrt C` fits below the cap.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingHighDensity.lean#L25-L57
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingHighDensity.lean#L25-L57

import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.shrinkingHighTolerance_eq_formula
    (P : ShrinkingBarrierRunData) {C : ℝ}
    (hC : 0 < C) (hcap : P.D / Real.sqrt C ≤ P.tau)
    {M m : ℕ} (hm : 1 ≤ m)
    (hCm : C * Real.log ((M : ℝ) + 2) ≤ (m : ℝ)) :
    shrinkingHighTolerance P M m =
      P.D * Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)) := by sorry
