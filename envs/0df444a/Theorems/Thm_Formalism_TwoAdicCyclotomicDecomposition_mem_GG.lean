-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_mem_GG
-- name    : Formalism.TwoAdicCyclotomicDecomposition.mem_GG
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:59:52.550773+00:00
-- url     : https://prove2.me/theorems/dbd1cf89-bf82-494c-a05f-f7e0b2efadeb
-- title:
--   Two Adic Cyclotomic Decomposition: mem GG
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the mem GG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L169-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L169-L172

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.mem_GG {s m : ℕ} (h : s ≤ m) (x : GalL (m + 2)) :
    x ∈ GG h ↔ resMap h x ∈ Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)) := by sorry
