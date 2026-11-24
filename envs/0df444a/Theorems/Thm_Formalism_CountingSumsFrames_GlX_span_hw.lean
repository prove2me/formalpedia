-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GlX_span_hw
-- name    : Formalism.CountingSumsFrames.GlX.span_hw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:22.588312+00:00
-- url     : https://prove2.me/theorems/fb6db1c8-1fe6-4624-b693-8703e6cffce0
-- title:
--   Gl X: span hw
-- statement:
--   The Gl X construction uses the span hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L120-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L120-L162

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

theorem Formalism.CountingSumsFrames.GlX.span_hw {W : Submodule K V} (hW : G.Stable W) {S : Finset (Fin r → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {ι : Type*} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hh0 : ∀ i, h i ≠ 0)
    (hsp : ∀ μ v, v ∈ W → G.IsHW μ v → v ∈ Submodule.span K (Set.range h)) :
    W ≤ ⨆ i, G.gS {h i} := by sorry
