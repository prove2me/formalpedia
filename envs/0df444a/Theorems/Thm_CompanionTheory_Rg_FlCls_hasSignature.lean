-- Prove2me | Theorems.Thm_CompanionTheory_Rg_FlCls_hasSignature
-- name    : CompanionTheory.Rg.FlCls.hasSignature
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:57:44.562491+00:00
-- url     : https://prove2.me/theorems/e6acfdac-c74d-49d3-b2d8-1a575717ffea
-- title:
--   Fl Cls: has Signature
-- statement:
--   The Fl Cls construction uses the has Signature property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/ArchimedeanDenseStabilizers/DenseRangeOfNotIsReal.lean#L62-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/ArchimedeanDenseStabilizers/DenseRangeOfNotIsReal.lean#L62-L105

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

theorem CompanionTheory.Rg.FlCls.hasSignature (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (hG : IsHermForm c G)
    (hc : ∀ (σ : E →+* ℂ) (x : E), σ (c x) = starRingEnd ℂ (σ x)) (τ : E →+* ℂ)
    (h : ∀ x : Fin n → E, x ≠ 0 → 0 < (τ (hermE c G x x)).re) :
    PI.UJClassFin.HasSignature (Gᵀ.map τ) n 0 := by sorry
