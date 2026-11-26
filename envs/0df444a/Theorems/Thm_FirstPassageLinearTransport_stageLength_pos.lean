-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageLength_pos
-- name    : FirstPassageLinearTransport.stageLength_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:56.52382+00:00
-- url     : https://prove2.me/theorems/26a67eb9-c5fc-4585-8d15-b21f5bdda174
-- title:
--   First Passage Linear Transport: stage Length pos
-- statement:
--   The First Passage Linear Transport construction uses the stage Length pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L184-L194
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L184-L194

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.stageLength_pos {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    1 ≤ stageLength p n := by sorry
