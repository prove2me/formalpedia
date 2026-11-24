-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_weight_wv_zero
-- name    : Formalism.CountingSumsFrames.weight_wv_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:24.706709+00:00
-- url     : https://prove2.me/theorems/e30cd1ed-9346-4f60-8a02-a4e353c9c49b
-- title:
--   Counting Sums Frames: weight wv zero
-- statement:
--   The Counting Sums Frames construction uses the weight wv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L729-L737
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L729-L737

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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.weight_wv_zero (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (m : Fin N × Fin r →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v) : Finsupp.weight (wv L J) m = 0 := by sorry
