-- Prove2me | Theorems.Thm_CompanionTheory_Rg_FlCls_exists_single_mem
-- name    : CompanionTheory.Rg.FlCls.exists_single_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:16:22.3144+00:00
-- url     : https://prove2.me/theorems/e4c14b55-7d7b-44f1-b584-f8caa0004cb7
-- title:
--   Fl Cls: exists single mem
-- statement:
--   The Fl Cls construction uses the exists single mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/ArchimedeanDenseStabilizers/DenseRangeOfNotIsReal.lean#L138-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/ArchimedeanDenseStabilizers/DenseRangeOfNotIsReal.lean#L138-L158

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

theorem CompanionTheory.Rg.FlCls.exists_single_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e →
      Pi.single i ((c : F) • e) ∈ (L : Set (Fin n → E)) := by sorry
