-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_landingBad_shrinking_high_density_le
-- name    : FirstPassageLinearTransport.card_landingBad_shrinking_high_density_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:37:14.915799+00:00
-- url     : https://prove2.me/theorems/342ad3b0-62d1-56cd-9c89-eeba1bb4c8d4
-- title:
--   First Passage Linear Transport: card landing Bad shrinking high density le
-- statement:
--   Density bound for every high first-passage landing target, including the
--   single upper power-of-two boundary point.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingHighDensity.lean#L117-L198
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingHighDensity.lean#L117-L198

import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.card_landingBad_shrinking_high_density_le
    (P : ShrinkingBarrierRunData) {C : ℝ}
    (hC : 0 < C) (hcap : P.D / Real.sqrt C ≤ P.tau)
    {M q : ℕ} (hq1 : 1 ≤ q)
    (hHigh : shrinkingSwitchRank C M ≤ q - 1) :
    ((landingBad q (shrinkingHighTolerance P M (q - 1))).card : ℝ) /
        (2 : ℝ) ^ q ≤
      Real.exp (-(Real.log 2 * (q : ℝ))) +
        quadraticWindowShellConstant / 2 *
          Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
            Real.log ((M : ℝ) + 2))) := by sorry
