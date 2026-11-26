-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_finsets_card_ge
-- name    : FirstPassageLinearTransport.card_finsets_card_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:30:18.506054+00:00
-- url     : https://prove2.me/theorems/ce372c95-2c35-564a-8b68-7fd1a8f0dc02
-- title:
--   First Passage Linear Transport: card finsets card ge
-- statement:
--   The First Passage Linear Transport construction uses the card finsets card ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L94-L123
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L94-L123

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.card_finsets_card_ge (r k : ℕ) (hk : k ≤ r) :
    Fintype.card {s : Finset (Fin r) // k ≤ s.card} = binomialUpperTail r k := by sorry
