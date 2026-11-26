-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bounded_passage_exists
-- name    : FirstPassageLinearTransport.bounded_passage_exists
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:04:49.819501+00:00
-- url     : https://prove2.me/theorems/7fa10286-9813-44c0-947d-1a950fccdb7e
-- title:
--   First Passage Linear Transport: bounded passage exists
-- statement:
--   The First Passage Linear Transport construction uses the bounded passage exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L157-L161
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L157-L161

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.bounded_passage_exists {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    ∃ k : ℕ, k ≤ M ∧ orbit k n ≤ targetScale r M := by sorry
