-- Prove2me | Theorems.Thm_FongoSync_Laws_state_set
-- name    : FongoSync.Laws.state_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:29.795561+00:00
-- url     : https://prove2.me/theorems/62c54792-013a-4f21-80ab-7bcc8aa76568
-- title:
--   Laws: state set
-- statement:
--   Replicas that applied the same set of changes hold the same state.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L109-L112
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L109-L112

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_IsCanonical_unique

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.state_set (σ : String → String → Strategy) (cs₁ cs₂ : List (Change V))
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (unique : ClockDetermines cs₁) :
    merged σ cs₁ = merged σ cs₂ := by sorry
