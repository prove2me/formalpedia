-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_one_sub_mul_mul_le
-- name    : Formalism.CountingSumsFrames.one_sub_mul_mul_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:27.997674+00:00
-- url     : https://prove2.me/theorems/ef50e520-ec89-4685-934c-c812d08f2f6b
-- title:
--   Counting Sums Frames: one sub mul mul le
-- statement:
--   The Counting Sums Frames construction uses the one sub mul mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrameMultinomialBoundHolds.lean#L84-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrameMultinomialBoundHolds.lean#L84-L95

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrameMultinomialBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Real
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.one_sub_mul_mul_le (y P W C x : ℝ) (n : ℕ) (hW : 0 ≤ W) (hP0 : 0 ≤ P) (hC : 0 ≤ C)
    (hPle : P ≤ (1 + x) ^ n * C) (hkey : (1 - y) * (1 + x) ^ n ≤ 1) : (1 - y) * (P * W) ≤ C * W := by sorry
