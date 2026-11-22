-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_sq_split
-- name    : Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.sq_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:39.790664+00:00
-- url     : https://prove2.me/theorems/5411ef2f-6d90-4f58-a837-242d2b235f5f
-- title:
--   Two Adic Valuation: sq split
-- statement:
--   The Two Adic Valuation construction uses the sq split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L32-L39

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation

theorem Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.sq_split (a : ℤ) (ha2 : a ^ 2 ≠ 1) :
    padicValInt 2 (a ^ 2 - 1) = padicValInt 2 (a - 1) + padicValInt 2 (a + 1) := by sorry
