-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_form_zero
-- name    : Formalism.CountingSumsFrames.TO.GlX.form_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:25.329801+00:00
-- url     : https://prove2.me/theorems/8ab67907-59f1-4b30-a309-a0faeb4af038
-- title:
--   Gl X: form zero
-- statement:
--   The Gl X construction uses the form zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1155-L1198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1155-L1198

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

theorem Formalism.CountingSumsFrames.TO.GlX.form_zero {W : Submodule K V} (hW : G.Stable W) {ι : Type} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hsp : W ≤ ⨆ i, G.gS {h i})
    (B : V →ₗ[K] V →ₗ[K] K) (hB : ∀ x ∈ W, ∀ y ∈ W, ∀ a b, B (G.E a b x) y = B x (G.E b a y))
    (h0 : ∀ i j, la i = la j → B (h i) (h j) = 0) : ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by sorry
