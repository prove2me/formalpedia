-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_closure_le_GG
-- name    : Formalism.TwoAdicCyclotomicDecomposition.closure_le_GG
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:59:55.531797+00:00
-- url     : https://prove2.me/theorems/bbf1a3a1-8509-4e4a-8c38-a2dfecae04bf
-- title:
--   Two Adic Cyclotomic Decomposition: closure le GG
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the closure le GG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L264-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L264-L272

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

theorem Formalism.TwoAdicCyclotomicDecomposition.closure_le_GG {s m : ℕ} (h : s ≤ m) :
    Subgroup.closure {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))}
      ≤ GG h := by sorry
