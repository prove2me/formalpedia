-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_eq_sum
-- name    : Formalism.CountingSumsFrames.TO.ext_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:54.245209+00:00
-- url     : https://prove2.me/theorems/d0c9d673-1400-448d-a0d0-91a70b7f062d
-- title:
--   TO: ext eq sum
-- statement:
--   The TO construction uses the ext eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L602-L613
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L602-L613

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

theorem Formalism.CountingSumsFrames.TO.ext_eq_sum (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (x : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hS : ∀ m ∈ x.support, ltr fs m ∈ S) : ext fs φ x = ∑ m ∈ S, φ (slc fs m x) * monomial m 1 := by sorry
