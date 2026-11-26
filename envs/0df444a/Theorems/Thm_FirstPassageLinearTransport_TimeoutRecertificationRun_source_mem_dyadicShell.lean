-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_source_mem_dyadicShell
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.source_mem_dyadicShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:17:46.468547+00:00
-- url     : https://prove2.me/theorems/cc0d18f1-2982-4810-a32d-81a1a1417d1e
-- title:
--   Timeout Recertification Run: source mem dyadic Shell
-- statement:
--   Every literal run retains the original outer-shell source.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L154-L162
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L154-L162

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.source_mem_dyadicShell
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    n ∈ dyadicShell M := by sorry
