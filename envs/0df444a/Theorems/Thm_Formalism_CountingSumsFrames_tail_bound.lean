-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_tail_bound
-- name    : Formalism.CountingSumsFrames.tail_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:01.737369+00:00
-- url     : https://prove2.me/theorems/7f1f9eb0-f5b9-444d-9511-ea987a362d87
-- title:
--   Counting Sums Frames: tail bound
-- statement:
--   The Counting Sums Frames construction uses the tail bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicLevelCountRec.lean#L101-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicLevelCountRec.lean#L101-L115

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
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
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.tail_bound (k' A B J : ℕ) (hJ : J ≤ min A B) :
    ((dimPol k' (A - J) * dimPol k' (B - J) : ℕ) : ℝ) ≤
      (1 - (J : ℝ) / (B + k' + 1)) ^ k' * ((dimPol k' A * dimPol k' B : ℕ) : ℝ) := by sorry
