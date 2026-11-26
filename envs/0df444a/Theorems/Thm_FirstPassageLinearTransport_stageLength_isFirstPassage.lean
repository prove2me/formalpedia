-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageLength_isFirstPassage
-- name    : FirstPassageLinearTransport.stageLength_isFirstPassage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:04:54.33311+00:00
-- url     : https://prove2.me/theorems/d78d98f4-781e-4ebb-bdd0-dab04e8bebcd
-- title:
--   First Passage Linear Transport: stage Length is First Passage
-- statement:
--   The First Passage Linear Transport construction uses the stage Length is First Passage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L176-L182
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L176-L182

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.stageLength_isFirstPassage {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    IsFirstPassage (targetScale r M) n (stageLength p n) := by sorry
