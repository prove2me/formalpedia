-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_elapsed_pos
-- name    : FirstPassageLinearTransport.RecertificationRun.elapsed_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:19.016312+00:00
-- url     : https://prove2.me/theorems/ce5d297c-788a-5cc1-a0b5-a76c7b85e54e
-- title:
--   Recertification Run: elapsed pos
-- statement:
--   The Recertification Run construction uses the elapsed pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationRun.lean#L55-L63
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationRun.lean#L55-L63

import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.RecertificationRun.elapsed_pos
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta} {n elapsed q : ℕ}
    (hrun : RecertificationRun p n elapsed q) : 0 < elapsed := by sorry
