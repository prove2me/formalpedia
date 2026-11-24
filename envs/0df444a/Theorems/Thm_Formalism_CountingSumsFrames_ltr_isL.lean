-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ltr_isL
-- name    : Formalism.CountingSumsFrames.ltr_isL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:50.459387+00:00
-- url     : https://prove2.me/theorems/59a6d48a-fc87-4860-9ca8-0c6bc4fb331d
-- title:
--   Counting Sums Frames: ltr is L
-- statement:
--   The Counting Sums Frames construction uses the ltr is L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L515-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L515-L519

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

theorem Formalism.CountingSumsFrames.ltr_isL (m : σ →₀ ℕ) : ∀ v, ltr fs m v ≠ 0 → ¬ fs v := by sorry
