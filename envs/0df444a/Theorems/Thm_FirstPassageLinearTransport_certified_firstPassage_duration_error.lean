-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_certified_firstPassage_duration_error
-- name    : FirstPassageLinearTransport.certified_firstPassage_duration_error
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:18:17.49626+00:00
-- url     : https://prove2.me/theorems/cd1b64b7-1db3-4168-bc85-60e394b1f720
-- title:
--   First Passage Linear Transport: certified first Passage duration error
-- statement:
--   A one-block duration lies within `durationError` of its deterministic
--   linear-drift center.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L38-L50
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L38-L50

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.certified_firstPassage_duration_error
    {x m q h : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood t)
    (hhm : h ≤ m) (hh : 0 < h)
    (hfp : IsFirstPassage (2 ^ q) x h) :
    |driftGap * (h : ℝ) - ((m : ℝ) - (q : ℝ))| ≤
      t * (m : ℝ) + t + 2 := by sorry
