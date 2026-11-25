-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_sum
-- name    : Formalism.CountingSumsFrames.TO.ext_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:24:31.625403+00:00
-- url     : https://prove2.me/theorems/7c586f8f-d4c1-4684-97ec-5735eeeccf8e
-- title:
--   TO: ext sum
-- statement:
--   The TO construction uses the ext sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L561-L564
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L561-L564

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
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem Formalism.CountingSumsFrames.TO.ext_sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ K →ₗ[K] MvPolynomial σ K) :
    ext fs (∑ i ∈ s, φ i) = ∑ i ∈ s, ext fs (φ i) := by sorry
