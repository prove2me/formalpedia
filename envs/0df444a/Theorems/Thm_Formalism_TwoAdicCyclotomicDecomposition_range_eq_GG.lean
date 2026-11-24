-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_range_eq_GG
-- name    : Formalism.TwoAdicCyclotomicDecomposition.range_eq_GG
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:59:59.129046+00:00
-- url     : https://prove2.me/theorems/123c1019-8fcb-4bc3-98d2-7a1189c0ec68
-- title:
--   Two Adic Cyclotomic Decomposition: range eq GG
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the range eq GG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L295-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L295-L297

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

theorem Formalism.TwoAdicCyclotomicDecomposition.range_eq_GG {s m : ℕ} (h : s ≤ m) : (psi h).range = GG h := by sorry
