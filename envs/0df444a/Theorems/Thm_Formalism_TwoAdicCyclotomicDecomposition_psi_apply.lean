-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_psi_apply
-- name    : Formalism.TwoAdicCyclotomicDecomposition.psi_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:59:29.734125+00:00
-- url     : https://prove2.me/theorems/63a20894-2a1f-4e28-bdad-cc8ee02819aa
-- title:
--   Two Adic Cyclotomic Decomposition: psi apply
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the psi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L235-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L235-L236

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

theorem Formalism.TwoAdicCyclotomicDecomposition.psi_apply {s m : ℕ} (h : s ≤ m) (e : ℤˣ) (k : Multiplicative (ZMod (2 ^ (m - s)))) :
    psi h (e, k) = (iota (m + 2) e * wgen s m ^ (Multiplicative.toAdd k).val, 1, 1) := by sorry
