-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_backPath
-- name    : CompanionTheory.RgExh.Hk.backPath
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:27.03791+00:00
-- url     : https://prove2.me/theorems/501405fd-7af6-5ed0-a494-d1663598b34b
-- title:
--   Hk: back Path
-- statement:
--   The Hk construction uses the back Path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/ScalarCharacters/ScalCharOfSimple.lean#L47-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/ScalarCharacters/ScalCharOfSimple.lean#L47-L72

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_ScalarCharacters_ScalCharOfSimple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}

theorem CompanionTheory.RgExh.Hk.backPath (hC : StepChar) (hV : NonVan) (hNS : NonScal) (hB : Back) :
    ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ), GoodPath χ ss → HasChar X χ → Nontrivial X.V →
      ScalChar (path X χ ss) (pathEnd χ ss) → ScalChar X χ ∧ SimplePath χ ss := by sorry
