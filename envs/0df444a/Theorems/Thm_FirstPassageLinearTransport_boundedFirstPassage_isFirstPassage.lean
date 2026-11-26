-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_boundedFirstPassage_isFirstPassage
-- name    : FirstPassageLinearTransport.boundedFirstPassage_isFirstPassage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:47.065098+00:00
-- url     : https://prove2.me/theorems/1945b410-9ab1-4336-946e-79d0ae447fa9
-- title:
--   First Passage Linear Transport: bounded First Passage is First Passage
-- statement:
--   The First Passage Linear Transport construction uses the bounded First Passage is First Passage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L67-L78
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L67-L78

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.boundedFirstPassage_isFirstPassage {Y H n : ℕ}
    (h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y) :
    IsFirstPassage Y n (boundedFirstPassage Y H n) := by sorry
