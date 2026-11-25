-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_omD_apply
-- name    : CompanionTheory.RgExh.Hk.fsb_omD_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:00:59.46463+00:00
-- url     : https://prove2.me/theorems/a58202ae-38e8-40cf-89ce-7e47ad75ca40
-- title:
--   Hk: fsb om D apply
-- statement:
--   The Hk construction uses the fsb om D apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L90-L92

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

theorem CompanionTheory.RgExh.Hk.fsb_omD_apply (M : GMod n) (g : Fin n → M.V) (a : Fin n) : omD M g a = -∑ c, M.E a c (g c) := by sorry
