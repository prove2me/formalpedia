-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_differential_commutes_weight_operator
-- name    : CompanionTheory.D.LK.differential_commutes_weight_operator
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:03.602021+00:00
-- url     : https://prove2.me/theorems/9bc7450d-98c3-4c03-8b71-ec4bef04723e
-- title:
--   LK: differential commutes weight operator
-- statement:
--   The LK construction uses the differential commutes weight operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L46-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialCommutesWeightOperator.lean#L46-L79

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

theorem CompanionTheory.D.LK.differential_commutes_weight_operator : ∀ (n : ℕ) (ε₀ ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), (∀ a b, ε a = ε b → ε₀ a = ε₀ b) → KRel ε E →
    ∀ c, Commute (Ft ε₀ E c) (bd ε E) := by sorry
