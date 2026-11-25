-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_scalChar_of_simple
-- name    : CompanionTheory.RgExh.Hk.scalChar_of_simple
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:08.994048+00:00
-- url     : https://prove2.me/theorems/211df932-41ce-41c7-8507-fc33d05ba759
-- title:
--   Hk: scal Char of simple
-- statement:
--   The Hk construction uses the scal Char of simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/ScalarCharacters/ScalCharOfSimple.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/ScalarCharacters/ScalCharOfSimple.lean#L29-L39

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

theorem CompanionTheory.RgExh.Hk.scalChar_of_simple (hQ : QdetEq) {X : GMod n} {χ : Fin n → ℂ} (hS : IsSimple X) (hH : HasChar X χ) :
    ScalChar X χ := by sorry
