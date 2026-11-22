-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_val_even
-- name    : Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.val_even
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:36.470881+00:00
-- url     : https://prove2.me/theorems/42bd442e-dcf0-4e3d-8721-cce71915da99
-- title:
--   Two Adic Valuation: val even
-- statement:
--   The Two Adic Valuation construction uses the val even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L41-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L41-L57

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

theorem Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.val_even (a : ℤ) (ha : Odd a) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (he : 0 < e) (hev : Even e) :
    padicValInt 2 (a ^ e - 1) + 1 = padicValInt 2 (a ^ 2 - 1) + padicValNat 2 e := by sorry
