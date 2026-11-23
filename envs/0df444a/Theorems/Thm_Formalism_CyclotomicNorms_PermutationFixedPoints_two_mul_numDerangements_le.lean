-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_two_mul_numDerangements_le
-- name    : Formalism.CyclotomicNorms.PermutationFixedPoints.two_mul_numDerangements_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:31.398581+00:00
-- url     : https://prove2.me/theorems/452fbeea-bdac-4e9b-8173-fe2c26cad07c
-- title:
--   Permutation Fixed Points: two mul num Derangements le
-- statement:
--   The Permutation Fixed Points construction uses the two mul num Derangements le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L27-L30

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

theorem Formalism.CyclotomicNorms.PermutationFixedPoints.two_mul_numDerangements_le (k : ℕ) (hk : 1 ≤ k) :
    2 * numDerangements k ≤ k.factorial := by sorry
