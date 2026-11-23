-- Prove2me | Theorems.Thm_CompanionTheory_D_Inhab_exp_entry
-- name    : CompanionTheory.D.Inhab.exp_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:50.539558+00:00
-- url     : https://prove2.me/theorems/71db3c03-d67b-4e3c-8f61-b4c27002e871
-- title:
--   Inhab: exp entry
-- statement:
--   The Inhab construction uses the exp entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/ExpEntry.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/ExpEntry.lean#L7-L23

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_ExpEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab

theorem CompanionTheory.D.Inhab.exp_entry (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by sorry
