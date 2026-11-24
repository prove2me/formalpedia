-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_eqExt_core
-- name    : Formalism.CountingSumsFrames.TO.GlX.eqExt_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:07.416781+00:00
-- url     : https://prove2.me/theorems/0ba3a782-74c8-4c8e-9f1e-db87d1a74a1a
-- title:
--   Gl X: eq Ext core
-- statement:
--   The Gl X construction uses the eq Ext core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1088-L1114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1088-L1114

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

theorem Formalism.CountingSumsFrames.TO.GlX.eqExt_core {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {ι : Type} [Fintype ι] [DecidableEq ι]
    (h g : ι → V) (la : ι → Fin r → ℤ) (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W)
    (hli : LinearIndependent K h) (hsp : W ≤ ⨆ i, G.gS {h i})
    (hg : ∀ i, G.IsHW (la i) (g i)) (hgW : ∀ i, g i ∈ W) :
    ∃ φ : V →ₗ[K] V, ∀ i c, φ (Lv G (h i) c) = Lv G (g i) c := by sorry
