-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageLength_le_shell
-- name    : FirstPassageLinearTransport.stageLength_le_shell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:05:57.23142+00:00
-- url     : https://prove2.me/theorems/f077ed51-8dec-4d5b-a7a6-eaa690e79e0e
-- title:
--   First Passage Linear Transport: stage Length le shell
-- statement:
--   The First Passage Linear Transport construction uses the stage Length le shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L169-L174
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L169-L174

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.stageLength_le_shell {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    stageLength p n ≤ M := by sorry
