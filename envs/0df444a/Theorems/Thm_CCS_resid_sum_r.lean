-- Prove2me | Theorems.Thm_CCS_resid_sum_r
-- name    : CCS.resid_sum_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:55:24.250802+00:00
-- url     : https://prove2.me/theorems/87f1497c-58fe-4cca-9853-3c92d1072c5b
-- title:
--   CCS: resid sum r
-- statement:
--   The CCS construction uses the resid sum r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L47-L50
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L47-L50

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.resid_sum_r {P Q : Process Name} {c : Set (semantics (.sum P Q)).Event}
    (h1 : ¬ ∃ e, Sum.inl e ∈ c) (h2 : ∃ f, Sum.inr f ∈ c) :
    resid (.sum P Q) c = resid Q {f | Sum.inr f ∈ c} := by sorry
