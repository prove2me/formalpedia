-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_gram_key
-- name    : Formalism.CountingSumsFrames.gram_key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:05.522299+00:00
-- url     : https://prove2.me/theorems/f060d66f-bb3e-477c-8881-378f0fc04def
-- title:
--   Counting Sums Frames: gram key
-- statement:
--   The Counting Sums Frames construction uses the gram key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrameMultinomialBoundHolds.lean#L56-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrameMultinomialBoundHolds.lean#L56-L70

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

theorem Formalism.CountingSumsFrames.gram_key (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : (n : ℝ) * x ≤ y) :
    (1 - y) * (1 + x) ^ n ≤ 1 := by sorry
