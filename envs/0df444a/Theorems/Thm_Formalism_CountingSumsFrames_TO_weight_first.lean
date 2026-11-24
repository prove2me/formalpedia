-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_weight_first
-- name    : Formalism.CountingSumsFrames.TO.weight_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:00.064472+00:00
-- url     : https://prove2.me/theorems/ac94b3ae-1101-4213-9c32-6493d0ec58b5
-- title:
--   TO: weight first
-- statement:
--   The TO construction uses the weight first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L891-L897
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L891-L897

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

theorem Formalism.CountingSumsFrames.TO.weight_first (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (m : Fin N × Fin r →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → fsj N r j0 v) : Finsupp.weight (wv L J) m = Finsupp.weight (wv L j0) m := by sorry
