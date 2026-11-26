-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_interval_card_landingBad_adjustable_le
-- name    : FirstPassageLinearTransport.eventually_interval_card_landingBad_adjustable_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:44:20.018207+00:00
-- url     : https://prove2.me/theorems/e9a6d364-1368-57a4-8744-c8c5fcfe4c65
-- title:
--   First Passage Linear Transport: eventually interval card landing Bad adjustable le
-- statement:
--   Once the terminal rank is beyond the startup threshold, the
--   entropy-sharp landing bound holds simultaneously at every higher rank in a
--   finite re-certification interval.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L263-L277
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L263-L277

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.eventually_interval_card_landingBad_adjustable_le
    {lambda t : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ L : ℕ in Filter.atTop, ∀ U q : ℕ, q ∈ Finset.Icc L U →
      ((landingBad q t).card : ℝ) ≤
        1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by sorry
