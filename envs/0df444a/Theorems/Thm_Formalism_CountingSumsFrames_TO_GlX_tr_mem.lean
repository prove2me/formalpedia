-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_tr_mem
-- name    : Formalism.CountingSumsFrames.TO.GlX.tr_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:05.856477+00:00
-- url     : https://prove2.me/theorems/87c73bed-670a-56d7-8204-81bbc2868ae4
-- title:
--   Gl X: tr mem
-- statement:
--   The Gl X construction uses the tr mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L379-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L379-L384

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
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.TO.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Formalism.CountingSumsFrames.TO.GlX.tr_mem {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) (y : LinearMap.range (Lv G h)) :
    tr G hk y ∈ LinearMap.range (Lv G h') := by sorry
