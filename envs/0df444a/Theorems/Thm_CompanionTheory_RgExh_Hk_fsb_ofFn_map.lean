-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_ofFn_map
-- name    : CompanionTheory.RgExh.Hk.fsb_ofFn_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:00:32.842892+00:00
-- url     : https://prove2.me/theorems/e726b3fd-76cd-4563-b6ca-ab0f46841557
-- title:
--   Hk: fsb of Fn map
-- statement:
--   The Hk construction uses the fsb of Fn map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L27-L36

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

theorem CompanionTheory.RgExh.Hk.fsb_ofFn_map (f : V →ₗ[ℂ] W) : ∀ (t : ℕ) (g : Fin t → Module.End ℂ V) (g' : Fin t → Module.End ℂ W),
    (∀ k v, f (g k v) = g' k (f v)) → ∀ v, f ((List.ofFn g).prod v) = (List.ofFn g').prod (f v) := by sorry
