-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_boolParityWord_mod
-- name    : FirstPassageLinearTransport.boolParityWord_mod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:03:03.995773+00:00
-- url     : https://prove2.me/theorems/cb0f62fc-60b1-5696-9fc9-0749ac3f5371
-- title:
--   First Passage Linear Transport: bool Parity Word mod
-- statement:
--   The First Passage Linear Transport construction uses the bool Parity Word mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L282-L286
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L282-L286

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.boolParityWord_mod (M n : ℕ) :
    boolParityWord M (n % (2 ^ M)) = boolParityWord M n := by sorry
