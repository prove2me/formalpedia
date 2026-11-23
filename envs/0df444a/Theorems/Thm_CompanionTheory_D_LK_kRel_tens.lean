-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_kRel_tens
-- name    : CompanionTheory.D.LK.kRel_tens
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:56.547137+00:00
-- url     : https://prove2.me/theorems/d263e8b4-788f-405f-b9be-b79c76491f78
-- title:
--   LK: k Rel tens
-- statement:
--   The LK construction uses the k Rel tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/GeneralizedVermaModulePolynomial.lean#L125-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/GeneralizedVermaModulePolynomial.lean#L125-L137

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_GeneralizedVermaModulePolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MvPolynomial
open scoped TensorProduct
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL GlobalTheory.CompanionTheory.DSVerma GlobalTheory.CompanionTheory.DSCover
open CompanionTheory.D.DSIC (KRel NC)

theorem CompanionTheory.D.LK.kRel_tens {n : ℕ} {ε : Fin n → Bool} {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
    {E : Fin n → Fin n → Module.End ℂ V} {M : Fin n → Fin n → Module.End ℂ Z} (hE : KRel ε E) (hM : GlRel M) :
    KRel ε fun a b => ((E a b).rTensor Z + (M a b).lTensor V : Module.End ℂ (V ⊗[ℂ] Z)) := by sorry
