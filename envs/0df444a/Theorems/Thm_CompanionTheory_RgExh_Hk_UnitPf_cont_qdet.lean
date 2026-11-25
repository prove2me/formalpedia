-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_cont_qdet
-- name    : CompanionTheory.RgExh.Hk.UnitPf.cont_qdet
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:19:24.601326+00:00
-- url     : https://prove2.me/theorems/699ae566-73af-4eeb-92a3-e8d5677cf2e3
-- title:
--   Unit Pf: cont qdet
-- statement:
--   The Unit Pf construction uses the cont qdet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/ContOfFnProd.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/ContOfFnProd.lean#L54-L59

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOneStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaMinorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PrincipalSumStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_ContOfFnProd
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
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet qminor Tm GlRel)
open CompanionTheory.RgExh
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem CompanionTheory.RgExh.Hk.UnitPf.cont_qdet {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (ℓ : Module.Dual ℂ W) (f : W) :
    Continuous (fun u : ℂ => ℓ (qdet E u f)) := by sorry
