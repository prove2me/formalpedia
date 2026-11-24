-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_fact_bound
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.fact_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:26.024995+00:00
-- url     : https://prove2.me/theorems/0050a7af-f4ae-421a-9156-13df758df500
-- title:
--   flip Two Three: fact bound
-- statement:
--   The flip Two Three construction uses the fact bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/GammaIntegralPolynomialBound.lean#L151-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/GammaIntegralPolynomialBound.lean#L151-L160

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

theorem Formalism.LogVandermondeBounds.flipTwoThree.fact_bound (a b N i : ℕ) (hab : a ≤ b) (hi : i ≤ N) :
    (a + N - i).factorial ≤ a.factorial * (b + N + 1) ^ (N + 1) := by sorry
