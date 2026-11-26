-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_boundedFirstPassage_spec
-- name    : FirstPassageLinearTransport.boundedFirstPassage_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:38.566334+00:00
-- url     : https://prove2.me/theorems/eaf3d76e-cd91-4473-a5cf-30203a945bbd
-- title:
--   First Passage Linear Transport: bounded First Passage spec
-- statement:
--   The First Passage Linear Transport construction uses the bounded First Passage spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L61-L65
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L61-L65

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.boundedFirstPassage_spec {Y H n : ℕ}
    (h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y) :
    orbit (boundedFirstPassage Y H n) n ≤ Y := by sorry
