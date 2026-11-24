-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_ops_keep_pred
-- name    : Formalism.CountingSumsFrames.TO.ops_keep_pred
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:54.228205+00:00
-- url     : https://prove2.me/theorems/b05ebee4-cba0-4a2c-8e2b-33648044c0da
-- title:
--   TO: ops keep pred
-- statement:
--   The TO construction uses the ops keep pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1405-L1417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1405-L1417

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

theorem Formalism.CountingSumsFrames.TO.ops_keep_pred (S : Set σ) (P : σ → Prop) (hS : ∀ v ∈ S, P v) {T : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ FockB.Ops S) (g : MvPolynomial σ k) (hg : ∀ m ∈ g.support, ∀ v, m v ≠ 0 → P v) :
    ∀ m ∈ (T g).support, ∀ v, m v ≠ 0 → P v := by sorry
