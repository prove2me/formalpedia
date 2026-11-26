-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_certified_landing_mem_lower_shell
-- name    : FirstPassageLinearTransport.certified_landing_mem_lower_shell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:11:42.355851+00:00
-- url     : https://prove2.me/theorems/7512c028-9e14-55c4-bdcf-7bc02394644a
-- title:
--   First Passage Linear Transport: certified landing mem lower shell
-- statement:
--   A certified point in the first-passage band is in the lower ordinary
--   dyadic shell, never at the upper power-of-two endpoint.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L110-L122
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L110-L122

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.certified_landing_mem_lower_shell
    {q y : ℕ} (hq : 1 ≤ q) {t : ℝ} (htA : t < a0)
    (hband : 2 ^ (q - 1) < y ∧ y ≤ 2 ^ q)
    (hgood : y ∈ initialWindowGood t) :
    y ∈ dyadicShell (q - 1) := by sorry
