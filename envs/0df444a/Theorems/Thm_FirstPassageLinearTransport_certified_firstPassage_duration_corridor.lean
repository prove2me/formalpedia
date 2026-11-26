-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_certified_firstPassage_duration_corridor
-- name    : FirstPassageLinearTransport.certified_firstPassage_duration_corridor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:11:55.594839+00:00
-- url     : https://prove2.me/theorems/f7599ee1-505a-4c39-b2dc-2eefa902a792
-- title:
--   First Passage Linear Transport: certified first Passage duration corridor
-- statement:
--   Linear form of the paper's one-block duration corridor.  Division by
--   `driftGap` is intentionally postponed; this form is more convenient for
--   integer time supports.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L127-L200
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L127-L200

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.certified_firstPassage_duration_corridor
    {x m q h : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood t)
    (hhm : h ≤ m) (hh : 0 < h)
    (hfp : IsFirstPassage (2 ^ q) x h) :
    (1 - t) * (m : ℝ) - (q : ℝ) ≤ driftGap * (h : ℝ) ∧
      driftGap * (h : ℝ) <
        (1 + t) * ((m : ℝ) + 1) - (q : ℝ) + 1 := by sorry
