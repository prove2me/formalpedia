-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_gen_kill
-- name    : Formalism.CountingSumsFrames.TO.GlX.gen_kill
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:43.585802+00:00
-- url     : https://prove2.me/theorems/b05fbcbb-855a-4813-b3b5-fdeafd3b286c
-- title:
--   Gl X: gen kill
-- statement:
--   The Gl X construction uses the gen kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L135-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L135-L150

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

theorem Formalism.CountingSumsFrames.TO.GlX.gen_kill {W : Submodule K V} (hW : G.Stable W) {S : Finset (Fin r → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) (hvW : v ∈ W)
    (hv0 : v ≠ 0) {μ ν : Fin r → ℤ} (hμ : DomW μ) (hle : Dle μ ν) (hne : Dle ν la → la ≠ μ) :
    ∀ x ∈ G.gS {v}, G.cprod (qlist S (GlW.casI μ)) (G.comp ν x) = 0 := by sorry
