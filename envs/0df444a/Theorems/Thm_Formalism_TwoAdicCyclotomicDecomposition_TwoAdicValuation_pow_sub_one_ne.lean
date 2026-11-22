-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_pow_sub_one_ne
-- name    : Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.pow_sub_one_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:28.906163+00:00
-- url     : https://prove2.me/theorems/deca5991-d54d-4805-8a6b-cffd65a21a76
-- title:
--   Two Adic Valuation: pow sub one ne
-- statement:
--   The Two Adic Valuation construction uses the pow sub one ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L17-L22

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

theorem Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.pow_sub_one_ne (a : ℤ) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (he : 0 < e) : a ^ e - 1 ≠ 0 := by sorry
