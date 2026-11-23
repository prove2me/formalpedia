-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_lift_evd
-- name    : CompanionTheory.D.LK.lift_evd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:32.078408+00:00
-- url     : https://prove2.me/theorems/1c81a3e5-30ef-42d9-ba19-5313dc8c0ddb
-- title:
--   LK: lift evd
-- statement:
--   The LK construction uses the lift evd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L100-L103

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem CompanionTheory.D.LK.lift_evd {ε : Fin n → Bool} (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (b : FreeAlgebra ℂ (Fin n))
    (x : Cn n V) : lift n φ (evd (Ft ε E) b x) = evd (Ft ε F) b (lift n φ x) := by sorry
