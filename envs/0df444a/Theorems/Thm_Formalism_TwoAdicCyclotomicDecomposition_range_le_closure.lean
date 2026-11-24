-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_range_le_closure
-- name    : Formalism.TwoAdicCyclotomicDecomposition.range_le_closure
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:59:54.339107+00:00
-- url     : https://prove2.me/theorems/8968f8ad-dbbe-4705-a24e-b2d1c44a398d
-- title:
--   Two Adic Cyclotomic Decomposition: range le closure
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the range le closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L274-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L274-L293

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

theorem Formalism.TwoAdicCyclotomicDecomposition.range_le_closure {s m : ℕ} (h : s ≤ m) :
    (psi h).range ≤
      Subgroup.closure {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))} := by sorry
