-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_Tm_affine
-- name    : CompanionTheory.RgExh.Hk.UnitPf.Tm_affine
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:18:05.563535+00:00
-- url     : https://prove2.me/theorems/433b93b6-5812-55c8-9ba0-fe5460d48a5a
-- title:
--   Unit Pf: Tm affine
-- statement:
--   The Unit Pf construction uses the Tm affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/ContOfFnProd.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/ContOfFnProd.lean#L45-L52

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

theorem CompanionTheory.RgExh.Hk.UnitPf.Tm_affine {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (u : ℂ) (k : ℂ) (a b : Fin n) :
    Tm E (u - k) a b = ((if a = b then algebraMap ℂ (Module.End ℂ W) (-k) else 0) + E a b) +
      u • (if a = b then (1 : Module.End ℂ W) else 0) := by sorry
