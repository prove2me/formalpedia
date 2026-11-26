-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_prefix_position_le_of_not_hitsBarrier
-- name    : FirstPassageLinearTransport.prefix_position_le_of_not_hitsBarrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:03:20.173191+00:00
-- url     : https://prove2.me/theorems/4016ccf3-af1b-4324-b15f-864db1346fb2
-- title:
--   First Passage Linear Transport: prefix position le of not hits Barrier
-- statement:
--   Avoiding the recursive barrier keeps every prefix position inside it.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L400-L447
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L400-L447

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

theorem FirstPassageLinearTransport.prefix_position_le_of_not_hitsBarrier :
    ∀ {r n : ℕ} {a : ℝ} {y : ℤ},
      ¬hitsBarrierFrom a r y (boolParityWord r n) →
      ∀ H : ℕ, H ≤ r →
        |(y : ℝ) + 2 * oddCount n H - H| ≤ a := by sorry
