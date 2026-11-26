-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_terminal_witness
-- name    : FirstPassageLinearTransport.terminal_witness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:08:56.489915+00:00
-- url     : https://prove2.me/theorems/fa39a48c-0006-4e3c-9056-1c5365ecef9d
-- title:
--   First Passage Linear Transport: terminal witness
-- statement:
--   The First Passage Linear Transport construction uses the terminal witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L138-L155
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L138-L155

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.terminal_witness {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    orbit M n ≤ targetScale r M := by sorry
