-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_two_mul_numDerangements_le_factorial
-- name    : Formalism.CyclotomicNorms.PermutationFixedPoints.two_mul_numDerangements_le_factorial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:46.381789+00:00
-- url     : https://prove2.me/theorems/e916f36b-81a7-4450-a9e3-40f6deccf05c
-- title:
--   Permutation Fixed Points: two mul num Derangements le factorial
-- statement:
--   The Permutation Fixed Points construction uses the two mul num Derangements le factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L7-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L7-L25

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.PermutationFixedPoints

theorem Formalism.CyclotomicNorms.PermutationFixedPoints.two_mul_numDerangements_le_factorial (m : ℕ) :
    2 * numDerangements (m + 1) ≤ (m + 1).factorial ∧
      2 * numDerangements (m + 2) ≤ (m + 2).factorial := by sorry
