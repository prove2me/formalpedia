-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutCertified_duration_error
-- name    : FirstPassageLinearTransport.timeoutCertified_duration_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:07.145114+00:00
-- url     : https://prove2.me/theorems/84d4b507-5711-4f78-9e72-34895f5a4ee2
-- title:
--   First Passage Linear Transport: timeout Certified duration error
-- statement:
--   A certified high block has the usual duration corridor.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L38-L47
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L38-L47

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutCertified_duration_error
    {x m q h : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood t)
    (hhm : h ≤ m) (hh : 0 < h)
    (hfp : IsFirstPassage (2 ^ q) x h) :
    |driftGap * (h : ℝ) - ((m : ℝ) - (q : ℝ))| ≤
      t * (m : ℝ) + t + 2 := by sorry
