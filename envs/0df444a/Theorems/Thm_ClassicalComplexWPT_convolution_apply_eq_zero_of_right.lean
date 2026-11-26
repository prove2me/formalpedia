-- Prove2me | Theorems.Thm_ClassicalComplexWPT_convolution_apply_eq_zero_of_right
-- name    : ClassicalComplexWPT.convolution_apply_eq_zero_of_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:08:59.456288+00:00
-- url     : https://prove2.me/theorems/2c0040bc-3756-57c5-a6f3-84516e321dfc
-- title:
--   Classical Complex WPT: convolution apply eq zero of right
-- statement:
--   The Classical Complex WPT construction uses the convolution apply eq zero of right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L103-L109
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L103-L109

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.convolution_apply_eq_zero_of_right {q p : OriginSeq} {n : ℕ}
    (hp : ∀ k ≤ n, p k = 0) : convolution q p n = 0 := by sorry
