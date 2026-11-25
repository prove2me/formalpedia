-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_eq_zero_of_off
-- name    : CompanionTheory.RgExh.Hk.UnitPf.eq_zero_of_off
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:18:12.193592+00:00
-- url     : https://prove2.me/theorems/3c1cd31d-f259-5794-9361-b3bd759c197a
-- title:
--   Unit Pf: eq zero of off
-- statement:
--   The Unit Pf construction uses the eq zero of off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/ContOfFnProd.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/ContOfFnProd.lean#L61-L65

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

theorem CompanionTheory.RgExh.Hk.UnitPf.eq_zero_of_off {g : ℂ → ℂ} (hg : Continuous g) (u₀ : ℂ) (h : ∀ u, u ≠ u₀ → g u = 0) : g u₀ = 0 := by sorry
