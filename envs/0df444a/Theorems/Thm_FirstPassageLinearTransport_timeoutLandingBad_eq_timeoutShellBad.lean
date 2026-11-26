-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutLandingBad_eq_timeoutShellBad
-- name    : FirstPassageLinearTransport.timeoutLandingBad_eq_timeoutShellBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:21:30.289129+00:00
-- url     : https://prove2.me/theorems/f3dc7138-e878-5703-835f-133338987cc4
-- title:
--   First Passage Linear Transport: timeout Landing Bad eq timeout Shell Bad
-- statement:
--   The First Passage Linear Transport construction uses the timeout Landing Bad eq timeout Shell Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean#L27-L30
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean#L27-L30

import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.timeoutLandingBad_eq_timeoutShellBad
    (K₀ : ℝ) (L p : ℕ) :
    timeoutLandingBad K₀ L p = timeoutShellBad K₀ L (p - 1) := by sorry
