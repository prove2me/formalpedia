-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_wt_om
-- name    : CompanionTheory.D.LK.wt_om
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:30.764718+00:00
-- url     : https://prove2.me/theorems/6cbeccfb-6d22-4ced-b51d-3695d15c62ab
-- title:
--   LK: wt om
-- statement:
--   The LK construction uses the wt om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L188-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L188-L204

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
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
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem CompanionTheory.D.LK.wt_om (ε : Fin n → Bool) : wt (om ε) = (2 : ℝ) • PI.UpqRep.rhoC ε := by sorry
