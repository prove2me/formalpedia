-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_frst_add
-- name    : Formalism.CountingSumsFrames.frst_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:08.59526+00:00
-- url     : https://prove2.me/theorems/ff525883-6069-473b-b7c1-ffdcfd34353d
-- title:
--   Counting Sums Frames: frst add
-- statement:
--   The Counting Sums Frames construction uses the frst add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L503-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L503-L505

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

theorem Formalism.CountingSumsFrames.frst_add (m m' : σ →₀ ℕ) : frst fs (m + m') = frst fs m + frst fs m' := by sorry
