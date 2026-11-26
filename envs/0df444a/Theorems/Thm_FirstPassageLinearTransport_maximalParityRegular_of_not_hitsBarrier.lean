-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_maximalParityRegular_of_not_hitsBarrier
-- name    : FirstPassageLinearTransport.maximalParityRegular_of_not_hitsBarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:03:39.656259+00:00
-- url     : https://prove2.me/theorems/54a0b4c4-8166-4054-997a-ffa08b87bd43
-- title:
--   First Passage Linear Transport: maximal Parity Regular of not hits Barrier
-- statement:
--   The First Passage Linear Transport construction uses the maximal Parity Regular of not hits Barrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L454-L464
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L454-L464

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

theorem FirstPassageLinearTransport.maximalParityRegular_of_not_hitsBarrier {M n : ℕ} {h : ℝ}
    (hgood : ¬hitsBarrierFrom (2 * h) M 0 (boolParityWord M n)) :
    MaximalParityRegular n M h := by sorry
