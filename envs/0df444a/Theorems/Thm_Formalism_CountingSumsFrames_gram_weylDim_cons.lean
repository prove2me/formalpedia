-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_gram_weylDim_cons
-- name    : Formalism.CountingSumsFrames.gram_weylDim_cons
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:28.223916+00:00
-- url     : https://prove2.me/theorems/9ee02291-d1ec-4bf3-93a5-fc755b0d04f8
-- title:
--   Counting Sums Frames: gram weyl Dim cons
-- statement:
--   The Counting Sums Frames construction uses the gram weyl Dim cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrameMultinomialBoundHolds.lean#L10-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrameMultinomialBoundHolds.lean#L10-L30

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

theorem Formalism.CountingSumsFrames.gram_weylDim_cons (n : ℕ) (A : ℤ) (μ : Fin n → ℤ) :
    weylDim (n + 1) (Fin.cons A μ : Fin (n + 1) → ℤ) =
      (∏ j : Fin n, ((((A - μ j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) * weylDim n μ := by sorry
