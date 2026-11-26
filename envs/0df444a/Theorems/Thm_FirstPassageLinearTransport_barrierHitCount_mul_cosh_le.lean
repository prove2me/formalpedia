-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_mul_cosh_le
-- name    : FirstPassageLinearTransport.barrierHitCount_mul_cosh_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:00:47.133485+00:00
-- url     : https://prove2.me/theorems/df9fe7d4-6b34-4696-8c0e-6ac2415620ac
-- title:
--   First Passage Linear Transport: barrier Hit Count mul cosh le
-- statement:
--   Finite pruned-tree cosh potential.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L119-L174
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L119-L174

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

theorem FirstPassageLinearTransport.barrierHitCount_mul_cosh_le
    (a θ : ℝ) (r : ℕ) (y : ℤ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    (barrierHitCount a r y : ℝ) * Real.cosh (θ * a) ≤
      (2 : ℝ) ^ r * Real.cosh (θ * (y : ℝ)) * Real.cosh θ ^ r := by sorry
