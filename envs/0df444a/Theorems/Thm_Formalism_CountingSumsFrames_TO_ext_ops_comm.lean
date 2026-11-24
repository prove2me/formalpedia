-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_ops_comm
-- name    : Formalism.CountingSumsFrames.TO.ext_ops_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:25.842541+00:00
-- url     : https://prove2.me/theorems/515824c9-7e09-4b8d-8e90-b0377c0d8793
-- title:
--   TO: ext ops comm
-- statement:
--   The TO construction uses the ext ops comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1419-L1439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1419-L1439

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
variable {k σ : Type} [Field k]

theorem Formalism.CountingSumsFrames.TO.ext_ops_comm [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs] (S : Set σ) (hS : ∀ v ∈ S, ¬ fs v)
    {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S)
    (φ : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (hφ : ∀ x, IsF fs (φ x)) (x : MvPolynomial σ k) :
    ext fs φ (T x) = T (ext fs φ x) := by sorry
