-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_hook_den_bounds
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.hook_den_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:44.130821+00:00
-- url     : https://prove2.me/theorems/6be98602-4b44-4b31-869b-2252224502f0
-- title:
--   flip Two Three: hook den bounds
-- statement:
--   The flip Two Three construction uses the hook den bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/GammaIntegralPolynomialBound.lean#L137-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/GammaIntegralPolynomialBound.lean#L137-L149

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset MeasureTheory

theorem Formalism.LogVandermondeBounds.flipTwoThree.hook_den_bounds (N : ℕ) (nu : Fin (N+1) → ℕ) (hnu : Antitone nu) (i j : Fin (N+1))
    (hij : i < j) :
    (1:ℝ) ≤ (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ) ∧
      (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ) ≤ (nu 0 : ℝ) + N + 1 := by sorry
