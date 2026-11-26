-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_safeTerminalSum_le_lowerTail
-- name    : FirstPassageLinearTransport.safeTerminalSum_le_lowerTail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:19.571817+00:00
-- url     : https://prove2.me/theorems/b5c4737e-8f24-4bc0-aeb4-df9cda819488
-- title:
--   First Passage Linear Transport: safe Terminal Sum le lower Tail
-- statement:
--   The First Passage Linear Transport construction uses the safe Terminal Sum le lower Tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3065-L3086
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3065-L3086

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.safeTerminalSum_le_lowerTail
    {u eps : ℝ} {r : ℕ}
    (hterminal : ∀ v : Fin r → Bool,
      ballotWordValue 1 v ≤ u →
        ((boolSupport v).card : ℝ) ≤ (3 / 4 - eps) * r) :
    safeTerminalSum u r 1 ≤
      (2 : ℝ) ^ r * threeQuarterLowerTailMass eps r := by sorry
