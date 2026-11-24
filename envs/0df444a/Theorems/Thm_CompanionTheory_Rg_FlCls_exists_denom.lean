-- Prove2me | Theorems.Thm_CompanionTheory_Rg_FlCls_exists_denom
-- name    : CompanionTheory.Rg.FlCls.exists_denom
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:57:17.164562+00:00
-- url     : https://prove2.me/theorems/58cd893d-28f2-42c8-ac4b-cc4007b37acf
-- title:
--   Fl Cls: exists denom
-- statement:
--   The Fl Cls construction uses the exists denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/ArchimedeanDenseStabilizers/DenseRangeOfNotIsReal.lean#L107-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/ArchimedeanDenseStabilizers/DenseRangeOfNotIsReal.lean#L107-L136

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem CompanionTheory.Rg.FlCls.exists_denom (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ (L : Set (Fin n → E)), ∀ i, IsIntegral ℤ ((c : F) • x i) := by sorry
