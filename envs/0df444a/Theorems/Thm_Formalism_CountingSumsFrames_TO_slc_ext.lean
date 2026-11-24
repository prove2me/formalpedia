-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_ext
-- name    : Formalism.CountingSumsFrames.TO.slc_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:08.509883+00:00
-- url     : https://prove2.me/theorems/c4834a7c-4c83-44f2-b7d5-69177b0723e4
-- title:
--   TO: slc ext
-- statement:
--   The TO construction uses the slc ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2502-L2511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2502-L2511

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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem Formalism.CountingSumsFrames.TO.slc_ext (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (hφ : ∀ x, IsF fs (φ x)) (m : σ →₀ ℕ)
    (x : MvPolynomial σ K) : slc fs m (ext fs φ x) = φ (slc fs m x) := by sorry
