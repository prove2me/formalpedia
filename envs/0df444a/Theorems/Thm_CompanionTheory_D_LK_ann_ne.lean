-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_ann_ne
-- name    : CompanionTheory.D.LK.ann_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:06.175317+00:00
-- url     : https://prove2.me/theorems/6bd9c692-17d4-4db5-9884-b541aaa3d0e4
-- title:
--   LK: ann ne
-- statement:
--   The LK construction uses the ann ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L26-L30

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

theorem CompanionTheory.D.LK.ann_ne {i : Pos n} {x : Cn n V} {A : Finset (Pos n)} (h : ann i x A ≠ 0) : i ∉ A ∧ x (insert i A) ≠ 0 := by sorry
