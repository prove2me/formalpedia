-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GlX_range_Lv
-- name    : Formalism.CountingSumsFrames.GlX.range_Lv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:21.588816+00:00
-- url     : https://prove2.me/theorems/6b5f07c7-3e52-4c13-a97f-355d9b6d6e88
-- title:
--   Gl X: range Lv
-- statement:
--   The Gl X construction uses the range Lv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L245-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L245-L263

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

theorem Formalism.CountingSumsFrames.GlX.range_Lv (v : V) : LinearMap.range (Lv G v) = G.gS {v} := by sorry
