-- Prove2me | Theorems.Thm_Formalism_GM_badCrit_core
-- name    : Formalism.GM.badCrit_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:37.111307+00:00
-- url     : https://prove2.me/theorems/fe85df5e-8179-46de-b052-bb0392e8fe60
-- title:
--   GM: bad Crit core
-- statement:
--   The GM construction uses the bad Crit core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L28-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L28-L64

import Definitions.Def_Formalism_MahlerMeasure_StatementT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Module

theorem Formalism.GM.badCrit_core {p : ℕ} [Fact p.Prime] {m : ℕ} (E : ℕ) (N : Submodule ℤ_[p] (Fin m → ℤ_[p]))
    (h : ∀ l : (Fin m → ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p], (∃ z, l z = 1) →
      ∃ v ∈ N, (p : ℝ) ^ (-(E : ℤ)) ≤ ‖l v‖) :
    ∀ z, (p : ℤ_[p]) ^ E • z ∈ N := by sorry
