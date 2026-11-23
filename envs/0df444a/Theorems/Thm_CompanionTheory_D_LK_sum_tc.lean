-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_sum_tc
-- name    : CompanionTheory.D.LK.sum_tc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:51:09.215891+00:00
-- url     : https://prove2.me/theorems/600eeb2b-47e1-4435-af98-a1c90592c99c
-- title:
--   LK: sum tc
-- statement:
--   The LK construction uses the sum tc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/KoszulDifferentialAnticommutator.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/KoszulDifferentialAnticommutator.lean#L21-L28

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

theorem CompanionTheory.D.LK.sum_tc {M : Type} [AddCommGroup M] [Module ℂ M] (i j : Pos n) (f : Pos n → M) :
    ∑ k, tc ε i j k • f k = if h : cpt ε i ∧ cpt ε j ∧ i.1.2 = j.1.1 then
      f ⟨(i.1.1, j.1.2), i.2.trans (h.2.2 ▸ j.2)⟩ else 0 := by sorry
