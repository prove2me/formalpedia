-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_weight_first
-- name    : Formalism.CountingSumsFrames.weight_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:35.308601+00:00
-- url     : https://prove2.me/theorems/8a96cb35-21ec-4f7b-8d5e-d2fdb2afeea7
-- title:
--   Counting Sums Frames: weight first
-- statement:
--   The Counting Sums Frames construction uses the weight first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L846-L854
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L846-L854

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

theorem Formalism.CountingSumsFrames.weight_first (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (m : Fin N × Fin r →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → fsj N r j0 v) : Finsupp.weight (wv L J) m = Finsupp.weight (wv L j0) m := by sorry
