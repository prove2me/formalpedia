-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_boundedFirstPassage_eq_find
-- name    : FirstPassageLinearTransport.boundedFirstPassage_eq_find
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:04:13.363926+00:00
-- url     : https://prove2.me/theorems/208c21b5-0cf7-5b48-8dec-0bdaabc0c2bb
-- title:
--   First Passage Linear Transport: bounded First Passage eq find
-- statement:
--   The First Passage Linear Transport construction uses the bounded First Passage eq find property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L48-L53
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L48-L53

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.boundedFirstPassage_eq_find {Y H n : ℕ}
    (h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y) :
    boundedFirstPassage Y H n = Nat.find h := by sorry
