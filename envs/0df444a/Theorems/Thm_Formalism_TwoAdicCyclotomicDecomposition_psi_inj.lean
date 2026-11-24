-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_psi_inj
-- name    : Formalism.TwoAdicCyclotomicDecomposition.psi_inj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:59:42.24389+00:00
-- url     : https://prove2.me/theorems/2317130f-93d8-4f4f-afd5-b8a5246d31e7
-- title:
--   Two Adic Cyclotomic Decomposition: psi inj
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the psi inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L238-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L238-L257

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

theorem Formalism.TwoAdicCyclotomicDecomposition.psi_inj {s m : ℕ} (h : s ≤ m) : Function.Injective (psi h) := by sorry
