-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GlX_tr_tr
-- name    : Formalism.CountingSumsFrames.GlX.tr_tr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:28.711795+00:00
-- url     : https://prove2.me/theorems/de216fd2-d8f6-48c7-a4f6-62f14eec91ea
-- title:
--   Gl X: tr tr
-- statement:
--   The Gl X construction uses the tr tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L346-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L346-L352

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Formalism.CountingSumsFrames.GlX.tr_tr {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h'))
    (hk' : LinearMap.ker (Lv G h') ≤ LinearMap.ker (Lv G h)) (y : LinearMap.range (Lv G h)) :
    tr G hk' ⟨tr G hk y, tr_mem G hk y⟩ = y := by sorry
