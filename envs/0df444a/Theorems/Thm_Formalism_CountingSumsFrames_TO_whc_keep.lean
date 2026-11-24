-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_whc_keep
-- name    : Formalism.CountingSumsFrames.TO.whc_keep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:05.79192+00:00
-- url     : https://prove2.me/theorems/a31d5bd8-8f11-4380-92fd-0afa81ad19e5
-- title:
--   TO: whc keep
-- statement:
--   The TO construction uses the whc keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1033-L1042
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1033-L1042

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

theorem Formalism.CountingSumsFrames.TO.whc_keep {σ M M' : Type} [AddCommMonoid M] [AddCommMonoid M'] (w : σ → M) (w' : σ → M') (ν : M')
    (D : M) {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] w D) :
    weightedHomogeneousComponent w' ν x ∈ weightedHomogeneousSubmodule ℚ_[p] w D := by sorry
