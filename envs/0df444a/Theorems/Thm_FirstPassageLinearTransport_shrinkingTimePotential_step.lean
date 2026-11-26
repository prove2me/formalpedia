-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingTimePotential_step
-- name    : FirstPassageLinearTransport.shrinkingTimePotential_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:33.539802+00:00
-- url     : https://prove2.me/theorems/76ddec62-2f63-567a-a355-30b32ae04809
-- title:
--   First Passage Linear Transport: shrinking Time Potential step
-- statement:
--   One deterministic rank step pays its complete corridor-width budget.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L147-L247
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L147-L247

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.shrinkingTimePotential_step
    (P : ShrinkingBarrierRunData) {M S qPrev m q : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) (hmPrev : qPrev = m + 1)
    (hq : if S ≤ m then
        (q : ℝ) ≤ (P.rHi : ℝ) * (m : ℝ)
      else (q : ℝ) ≤ (P.rLo : ℝ) * (m : ℝ)) :
    (if S ≤ m then durationError (shrinkingHighTolerance P M m) m
      else durationError P.etaLo m) + shrinkingTimePotential P M S q ≤
        shrinkingTimePotential P M S qPrev := by sorry
