-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_hasChar_surj
-- name    : CompanionTheory.RgExh.Hk.fsb_hasChar_surj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:00:54.821231+00:00
-- url     : https://prove2.me/theorems/42d8a7aa-1e51-42a4-a982-650d3d51f95d
-- title:
--   Hk: fsb has Char surj
-- statement:
--   The Hk construction uses the fsb has Char surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L76-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L76-L88

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatementStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
variable {n : ℕ}

theorem CompanionTheory.RgExh.Hk.fsb_hasChar_surj (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (hs : Function.Surjective f) (χ : Fin n → ℂ) (h : HasChar M1 χ) : HasChar M2 χ := by sorry
