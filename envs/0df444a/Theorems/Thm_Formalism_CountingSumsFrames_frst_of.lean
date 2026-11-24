-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_frst_of
-- name    : Formalism.CountingSumsFrames.frst_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:31.03892+00:00
-- url     : https://prove2.me/theorems/2da3f4c3-f0dc-461b-b2b8-9995f566066f
-- title:
--   Counting Sums Frames: frst of
-- statement:
--   The Counting Sums Frames construction uses the frst of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L487-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L487-L489

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

theorem Formalism.CountingSumsFrames.frst_of {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → fs v) : frst fs m = m := by sorry
