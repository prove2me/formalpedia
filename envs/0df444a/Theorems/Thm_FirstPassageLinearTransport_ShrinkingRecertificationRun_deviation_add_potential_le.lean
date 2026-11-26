-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_deviation_add_potential_le
-- name    : FirstPassageLinearTransport.ShrinkingRecertificationRun.deviation_add_potential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:01.095969+00:00
-- url     : https://prove2.me/theorems/349e5a69-e776-4be5-8c7f-324678936a8e
-- title:
--   Shrinking Recertification Run: deviation add potential le
-- statement:
--   Every literal run stays in one deterministic interval around the linear
--   drift time.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L251-L408
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L251-L408

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.ShrinkingRecertificationRun.deviation_add_potential_le
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hM : 1 ≤ M)
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    |driftGap * (elapsed : ℝ) - (((M + 1 : ℕ) : ℝ) - (q : ℝ))| +
        shrinkingTimePotential P M S q ≤
      shrinkingTimePotential P M S (M + 1) := by sorry
