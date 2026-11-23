-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_filter_erase_of_not
-- name    : CompanionTheory.D.LK.filter_erase_of_not
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:42.808943+00:00
-- url     : https://prove2.me/theorems/77a557e5-a60d-4a3d-ac79-df6f0cc29d22
-- title:
--   LK: filter erase of not
-- statement:
--   The LK construction uses the filter erase of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L90-L94

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

theorem CompanionTheory.D.LK.filter_erase_of_not {p : Pos n → Prop} [DecidablePred p] {k : Pos n} (hk : ¬p k) (A : Finset (Pos n)) :
    (A.erase k).filter p = A.filter p := by sorry
