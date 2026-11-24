-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_cprod_mod
-- name    : Formalism.CountingSumsFrames.TO.GlX.cprod_mod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:54.534035+00:00
-- url     : https://prove2.me/theorems/c9bb71b4-1a49-4640-acb0-ec58c7099226
-- title:
--   Gl X: cprod mod
-- statement:
--   The Gl X construction uses the cprod mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L99-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L99-L116

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.TO.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Formalism.CountingSumsFrames.TO.GlX.cprod_mod {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) (cs : List ℤ) :
    G.cprod cs v - (cs.map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod • v ∈ U := by sorry
