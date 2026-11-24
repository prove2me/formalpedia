-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_frst_add_ltr
-- name    : Formalism.CountingSumsFrames.frst_add_ltr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:52.979031+00:00
-- url     : https://prove2.me/theorems/900b3156-caa1-43bd-ab93-38e5b354747c
-- title:
--   Counting Sums Frames: frst add ltr
-- statement:
--   The Counting Sums Frames construction uses the frst add ltr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L483-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L483-L485

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

theorem Formalism.CountingSumsFrames.frst_add_ltr (m : σ →₀ ℕ) : frst fs m + ltr fs m = m := by sorry
