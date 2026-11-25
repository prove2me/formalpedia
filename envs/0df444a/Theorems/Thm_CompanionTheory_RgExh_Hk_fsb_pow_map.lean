-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_pow_map
-- name    : CompanionTheory.RgExh.Hk.fsb_pow_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:00:56.214591+00:00
-- url     : https://prove2.me/theorems/adb38494-1bad-4f7c-8586-570a065b9ee6
-- title:
--   Hk: fsb pow map
-- statement:
--   The Hk construction uses the fsb pow map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L18-L25

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

theorem CompanionTheory.RgExh.Hk.fsb_pow_map (f : V →ₗ[ℂ] W) (T : Module.End ℂ V) (T' : Module.End ℂ W)
    (h : ∀ v, f (T v) = T' (f v)) : ∀ (k : ℕ) (v : V), f ((T ^ k) v) = (T' ^ k) (f v) := by sorry
