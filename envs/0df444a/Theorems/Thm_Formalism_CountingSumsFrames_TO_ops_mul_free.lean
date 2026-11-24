-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_ops_mul_free
-- name    : Formalism.CountingSumsFrames.TO.ops_mul_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:59.587967+00:00
-- url     : https://prove2.me/theorems/795176e7-724b-4ee2-accc-99796df5bd88
-- title:
--   TO: ops mul free
-- statement:
--   The TO construction uses the ops mul free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1387-L1403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1387-L1403

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

theorem Formalism.CountingSumsFrames.TO.ops_mul_free (S : Set σ) {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S)
    (q : MvPolynomial σ k) (hq : ∀ m ∈ q.support, ∀ v ∈ S, m v = 0) (g : MvPolynomial σ k) :
    T (g * q) = T g * q := by sorry
