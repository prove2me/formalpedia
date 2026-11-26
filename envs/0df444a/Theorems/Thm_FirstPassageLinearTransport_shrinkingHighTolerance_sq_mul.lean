-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingHighTolerance_sq_mul
-- name    : FirstPassageLinearTransport.shrinkingHighTolerance_sq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:33.374467+00:00
-- url     : https://prove2.me/theorems/9b770bee-f095-5c0e-a3fb-35dc2aaca997
-- title:
--   First Passage Linear Transport: shrinking High Tolerance sq mul
-- statement:
--   Exact quadratic exponent at every high rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingHighDensity.lean#L60-L74
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingHighDensity.lean#L60-L74

import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.shrinkingHighTolerance_sq_mul
    (P : ShrinkingBarrierRunData) {C : ℝ}
    (hC : 0 < C) (hcap : P.D / Real.sqrt C ≤ P.tau)
    {M m : ℕ} (hm : 1 ≤ m)
    (hCm : C * Real.log ((M : ℝ) + 2) ≤ (m : ℝ)) :
    shrinkingHighTolerance P M m ^ 2 * (m : ℝ) =
      P.D ^ 2 * Real.log ((M : ℝ) + 2) := by sorry
