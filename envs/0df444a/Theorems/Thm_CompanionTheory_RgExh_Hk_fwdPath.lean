-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_fwdPath
-- name    : CompanionTheory.RgExh.Hk.fwdPath
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:30.322785+00:00
-- url     : https://prove2.me/theorems/8336c5b3-08d5-4760-bb13-cb1477a84a10
-- title:
--   Hk: fwd Path
-- statement:
--   The Hk construction uses the fwd Path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/ScalarCharacters/ScalCharOfSimple.lean#L74-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/ScalarCharacters/ScalCharOfSimple.lean#L74-L104

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

theorem CompanionTheory.RgExh.Hk.fwdPath (hQ : QdetEq) (hC : StepChar) (hOS : OmScal) (hF : FwdSimple) (hR : Reflect) :
    ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ), GoodPath χ ss → SimplePath χ ss → IsSimple X →
      HasChar X χ → IsSimple (path X χ ss) ∧
        ∀ X' : GMod n, IsSimple X' → HasChar X' χ → Iso (path X χ ss) (path X' χ ss) → Iso X X' := by sorry
