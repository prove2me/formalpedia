-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ext_sum
-- name    : Formalism.CountingSumsFrames.ext_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:23:37.522976+00:00
-- url     : https://prove2.me/theorems/682ef50a-43cb-4f87-95f7-4ec4853a6ed4
-- title:
--   Counting Sums Frames: ext sum
-- statement:
--   The Counting Sums Frames construction uses the ext sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L547-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L547-L555

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem Formalism.CountingSumsFrames.ext_sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ K →ₗ[K] MvPolynomial σ K) :
    ext fs (∑ i ∈ s, φ i) = ∑ i ∈ s, ext fs (φ i) := by sorry
