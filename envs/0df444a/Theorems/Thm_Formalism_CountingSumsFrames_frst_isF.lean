-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_frst_isF
-- name    : Formalism.CountingSumsFrames.frst_isF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:41.911269+00:00
-- url     : https://prove2.me/theorems/6e0522e5-5ebc-487c-96ac-119def6cbdc0
-- title:
--   Counting Sums Frames: frst is F
-- statement:
--   The Counting Sums Frames construction uses the frst is F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L509-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L509-L514

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

theorem Formalism.CountingSumsFrames.frst_isF (m : σ →₀ ℕ) : ∀ v, frst fs m v ≠ 0 → fs v := by sorry
