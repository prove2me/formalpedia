-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_nontrivial_step
-- name    : CompanionTheory.RgExh.Hk.nontrivial_step
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:40.72791+00:00
-- url     : https://prove2.me/theorems/dee4330d-7129-5c78-ba45-c41b672faa7c
-- title:
--   Hk: nontrivial step
-- statement:
--   The Hk construction uses the nontrivial step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/ScalarCharacters/ScalCharOfSimple.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/ScalarCharacters/ScalCharOfSimple.lean#L41-L45

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

theorem CompanionTheory.RgExh.Hk.nontrivial_step (hV : NonVan) {X : GMod n} {χ : Fin n → ℂ} {s : Fin n} (hH : HasChar X χ)
    (hN : Nontrivial X.V) (hf : ∀ r, χ r ≠ χ s + 1) : Nontrivial (step X (χ s)).V := by sorry
