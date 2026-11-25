-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_tensVd_apply
-- name    : CompanionTheory.RgExh.Hk.fsb_tensVd_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:59:34.982415+00:00
-- url     : https://prove2.me/theorems/22492e6b-bea3-519b-ad40-5335d873c9fb
-- title:
--   Hk: fsb tens Vd apply
-- statement:
--   The Hk construction uses the fsb tens Vd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L94-L97

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

theorem CompanionTheory.RgExh.Hk.fsb_tensVd_apply (M : GMod n) (a b : Fin n) (g : Fin n → M.V) (d : Fin n) :
    tensVd M.E a b g d = M.E a b (g d) - if d = b then g a else 0 := by sorry
