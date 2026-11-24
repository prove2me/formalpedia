-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_monomial
-- name    : Formalism.CountingSumsFrames.TO.ext_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:43.648525+00:00
-- url     : https://prove2.me/theorems/521dd523-2889-4197-92a7-df9f1f93d3f2
-- title:
--   TO: ext monomial
-- statement:
--   The TO construction uses the ext monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L546-L549
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L546-L549

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

theorem Formalism.CountingSumsFrames.TO.ext_monomial (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (m : σ →₀ ℕ) (a : K) :
    ext fs φ (monomial m a) = a • (φ (monomial (frst fs m) 1) * monomial (ltr fs m) 1) := by sorry
