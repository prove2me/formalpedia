-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_interval_rankTransport_small
-- name    : FirstPassageLinearTransport.eventually_interval_rankTransport_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:37:15.632912+00:00
-- url     : https://prove2.me/theorems/afd2fe48-611d-5dd4-be57-a89e970bd6ec
-- title:
--   First Passage Linear Transport: eventually interval rank Transport small
-- statement:
--   Interval form consumed by finite terminal profiles.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankTransportAsymptotics.lean#L97-L106
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankTransportAsymptotics.lean#L97-L106

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_interval_rankTransport_small
    {r : ℚ} (hr : 0 < r) :
    ∀ᶠ L : ℕ in atTop, ∀ U q : ℕ, q ∈ Finset.Icc L U →
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3 := by sorry
