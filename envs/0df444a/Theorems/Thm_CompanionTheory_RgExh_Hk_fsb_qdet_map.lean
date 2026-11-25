-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_qdet_map
-- name    : CompanionTheory.RgExh.Hk.fsb_qdet_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:09:35.624794+00:00
-- url     : https://prove2.me/theorems/af844b39-8eb8-4a99-bdf7-1e3198c68db0
-- title:
--   Hk: fsb qdet map
-- statement:
--   The Hk construction uses the fsb qdet map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L38-L48

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
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem CompanionTheory.RgExh.Hk.fsb_qdet_map {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (hf : ∀ a b v, f (E a b v) = E' a b (f v)) (x : ℂ) (v : V) :
    f (qdet E x v) = qdet E' x (f v) := by sorry
