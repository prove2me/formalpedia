-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_badCount_le_shell_sum
-- name    : FirstPassageLinearTransport.badCount_le_shell_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:41.202326+00:00
-- url     : https://prove2.me/theorems/dab2d9cb-2ec3-4402-9b27-e6e597d51044
-- title:
--   First Passage Linear Transport: bad Count le shell sum
-- statement:
--   The First Passage Linear Transport construction uses the bad Count le shell sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L142-L153
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L142-L153

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.badCount_le_shell_sum (S : Set ℕ) (X : ℕ) :
    badCount S X ≤
      ∑ M ∈ Finset.range (Nat.log 2 X + 1), (shellBad S M).card := by sorry
