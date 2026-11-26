-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_shellMaximalParityBad_le
-- name    : FirstPassageLinearTransport.card_shellMaximalParityBad_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:03:33.424662+00:00
-- url     : https://prove2.me/theorems/4d8a039c-fe75-5f7f-bc91-3df2c1c1785f
-- title:
--   First Passage Linear Transport: card shell Maximal Parity Bad le
-- statement:
--   The shellwise maximal-parity exceptional set obeys the optimized
--   two-sided Boolean-barrier estimate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L483-L495
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L483-L495

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

theorem FirstPassageLinearTransport.card_shellMaximalParityBad_le {M : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hM : 0 < M) :
    ((shellMaximalParityBad M h).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-(2 * h ^ 2 / (M : ℝ))) := by sorry
