-- Prove2me | Theorems.Thm_CCS_resid_sum_none
-- name    : CCS.resid_sum_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:22.558706+00:00
-- url     : https://prove2.me/theorems/bc32d798-bdc7-4bd1-9a13-4c8e8c417509
-- title:
--   CCS: resid sum none
-- statement:
--   The CCS construction uses the resid sum none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L52-L55
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L52-L55

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.resid_sum_none {P Q : Process Name} {c : Set (semantics (.sum P Q)).Event}
    (h1 : ¬ ∃ e, Sum.inl e ∈ c) (h2 : ¬ ∃ f, Sum.inr f ∈ c) :
    resid (.sum P Q) c = .sum P Q := by sorry
