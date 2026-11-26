-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_certified_endpoint_shell_eq
-- name    : FirstPassageLinearTransport.ShrinkingRecertificationRun.certified_endpoint_shell_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:11:32.095116+00:00
-- url     : https://prove2.me/theorems/d968381d-3e9d-5866-984d-0995f2bc4df8
-- title:
--   Shrinking Recertification Run: certified endpoint shell eq
-- statement:
--   A certified checkpoint following a run is in the unique lower shell
--   `q-1`; this is the deterministic-rank input to time compression.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L182-L202
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L182-L202

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.ShrinkingRecertificationRun.certified_endpoint_shell_eq
    {P : ShrinkingBarrierRunData} {M S n elapsed q m : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q)
    {t : ℝ} (htA : t < a0)
    (hgood : orbit elapsed n ∈ initialWindowGood t)
    (hshell : orbit elapsed n ∈ dyadicShell m) :
    m = q - 1 := by sorry
