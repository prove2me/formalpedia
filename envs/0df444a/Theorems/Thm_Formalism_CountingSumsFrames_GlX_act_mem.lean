-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GlX_act_mem
-- name    : Formalism.CountingSumsFrames.GlX.act_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:27.823188+00:00
-- url     : https://prove2.me/theorems/00a4979a-9755-4094-9920-24798c4c3493
-- title:
--   Gl X: act mem
-- statement:
--   The Gl X construction uses the act mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L233-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L233-L237

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

theorem Formalism.CountingSumsFrames.GlX.act_mem {U : Submodule K V} (hU : G.Stable U) (w : List (Fin r × Fin r)) {x : V} (hx : x ∈ U) :
    act G w x ∈ U := by sorry
