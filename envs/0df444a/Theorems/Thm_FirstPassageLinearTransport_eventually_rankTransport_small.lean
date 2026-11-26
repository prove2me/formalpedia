-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_rankTransport_small
-- name    : FirstPassageLinearTransport.eventually_rankTransport_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:24:54.158126+00:00
-- url     : https://prove2.me/theorems/803da4ea-c12f-5bb5-96cd-74bd44e7de9c
-- title:
--   First Passage Linear Transport: eventually rank Transport small
-- statement:
--   The rescaled first-passage distortion startup is automatic beyond one
--   rank depending only on the positive common contraction budget.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankTransportAsymptotics.lean#L26-L94
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankTransportAsymptotics.lean#L26-L94

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_rankTransport_small
    {r : ℚ} (hr : 0 < r) :
    ∀ᶠ q : ℕ in atTop,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3 := by sorry
