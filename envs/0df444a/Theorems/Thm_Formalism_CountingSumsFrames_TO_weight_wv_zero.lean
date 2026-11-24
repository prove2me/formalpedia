-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_weight_wv_zero
-- name    : Formalism.CountingSumsFrames.TO.weight_wv_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:00.51583+00:00
-- url     : https://prove2.me/theorems/4d826818-7912-431e-83fc-1ae8d2368947
-- title:
--   TO: weight wv zero
-- statement:
--   The TO construction uses the weight wv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L760-L766
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L760-L766

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.weight_wv_zero (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (m : Fin N × Fin r →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v) : Finsupp.weight (wv L J) m = 0 := by sorry
