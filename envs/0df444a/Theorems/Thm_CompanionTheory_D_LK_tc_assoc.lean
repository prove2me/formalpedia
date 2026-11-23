-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_tc_assoc
-- name    : CompanionTheory.D.LK.tc_assoc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:48.262443+00:00
-- url     : https://prove2.me/theorems/a4f958ae-5c60-4b39-8389-c077b8fcdda6
-- title:
--   LK: tc assoc
-- statement:
--   The LK construction uses the tc assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/KoszulDifferentialAnticommutator.lean#L30-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/KoszulDifferentialAnticommutator.lean#L30-L46

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator
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
variable {n : ℕ} {ε : Fin n → Bool}

theorem CompanionTheory.D.LK.tc_assoc (p q r k : Pos n) : ∑ i, tc ε p q i * tc ε i r k = ∑ j, tc ε q r j * tc ε p j k := by sorry
