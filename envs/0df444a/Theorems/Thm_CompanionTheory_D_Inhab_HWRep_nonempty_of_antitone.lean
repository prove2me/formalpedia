-- Prove2me | Theorems.Thm_CompanionTheory_D_Inhab_HWRep_nonempty_of_antitone
-- name    : CompanionTheory.D.Inhab.HWRep.nonempty_of_antitone
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:37.993644+00:00
-- url     : https://prove2.me/theorems/1e45591d-deea-4e4c-8a95-302144cabc86
-- title:
--   HWRep: nonempty of antitone
-- statement:
--   The HWRep construction uses the nonempty of antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/NonemptyOfAntitone.lean#L151-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/NonemptyOfAntitone.lean#L151-L174

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab
attribute [instance] HWRep.fin HWRep.dec
open CompanionTheory.D.Inhab.HWRep
variable {k : ℕ}

theorem CompanionTheory.D.Inhab.HWRep.nonempty_of_antitone (ν : Fin k → ℤ) (hν : Antitone ν) : Nonempty (HWRep k ν) := by sorry
