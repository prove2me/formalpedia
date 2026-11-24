-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_eqExt
-- name    : Formalism.CountingSumsFrames.TO.GlX.eqExt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:32.04444+00:00
-- url     : https://prove2.me/theorems/ea893139-b5e8-4a9b-8362-c60677093f17
-- title:
--   Gl X: eq Ext
-- statement:
--   The Gl X construction uses the eq Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1116-L1153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1116-L1153

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

theorem Formalism.CountingSumsFrames.TO.GlX.eqExt {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {ι : Type} [Fintype ι] [DecidableEq ι]
    (h g : ι → V) (la : ι → Fin r → ℤ) (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W)
    (hli : LinearIndependent K h) (hsp : W ≤ ⨆ i, G.gS {h i})
    (hg : ∀ i, G.IsHW (la i) (g i)) (hgW : ∀ i, g i ∈ W) :
    ∃ φ : V →ₗ[K] V, (∀ i, φ (h i) = g i) ∧ (∀ x ∈ W, ∀ a b, φ (G.E a b x) = G.E a b (φ x)) ∧
      (∀ x ∈ W, φ x ∈ W) ∧ (∀ i, ∀ x ∈ G.gS {h i}, φ x ∈ G.gS {g i}) ∧
      (∀ i, g i ≠ 0 → ∀ x ∈ G.gS {h i}, φ x = 0 → x = 0) ∧
      (∀ i, g i = h i → ∀ x ∈ G.gS {h i}, φ x = x) ∧ (∀ i, g i = 0 → ∀ x ∈ G.gS {h i}, φ x = 0) := by sorry
