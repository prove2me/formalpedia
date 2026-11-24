-- Prove2me | Theorems.Thm_CompanionTheory_Rg_FlCls_denseRange_of_not_isReal
-- name    : CompanionTheory.Rg.FlCls.denseRange_of_not_isReal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:57:49.388818+00:00
-- url     : https://prove2.me/theorems/e4c5bf4a-4b26-4813-a0d2-446ff6405105
-- title:
--   Fl Cls: dense Range of not is Real
-- statement:
--   The Fl Cls construction uses the dense Range of not is Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/ArchimedeanDenseStabilizers/DenseRangeOfNotIsReal.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/ArchimedeanDenseStabilizers/DenseRangeOfNotIsReal.lean#L13-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_NefEffectiveCones_ExistsNsmulMulVecMemHat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFinite
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UJClassFin
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_ArchimedeanDenseStabilizers_DenseRangeOfNotIsReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix ComplexOrder MatrixOrder
open CompanionTheory CompanionTheory.Rg CompanionTheory.Rg.FlCls

theorem CompanionTheory.Rg.FlCls.denseRange_of_not_isReal {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ ComplexEmbedding.IsReal σ) : DenseRange σ := by sorry
