-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_succ_of_safe
-- name    : FirstPassageLinearTransport.barrierHitCount_succ_of_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:02:29.875037+00:00
-- url     : https://prove2.me/theorems/01e631fb-3e92-5e9b-ac34-8749d5ecc1a6
-- title:
--   First Passage Linear Transport: barrier Hit Count succ of safe
-- statement:
--   The First Passage Linear Transport construction uses the barrier Hit Count succ of safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L81-L100
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L81-L100

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

theorem FirstPassageLinearTransport.barrierHitCount_succ_of_safe {a : ℝ} {r : ℕ} {y : ℤ}
    (hy : ¬a < |(y : ℝ)|) :
    barrierHitCount a (r + 1) y =
      barrierHitCount a r (y - 1) + barrierHitCount a r (y + 1) := by sorry
