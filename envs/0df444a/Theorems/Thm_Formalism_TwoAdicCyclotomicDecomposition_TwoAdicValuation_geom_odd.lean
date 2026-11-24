-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_geom_odd
-- name    : Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.geom_odd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:05.160833+00:00
-- url     : https://prove2.me/theorems/4cbd681b-79de-43ea-9709-c190e9b1032e
-- title:
--   Two Adic Valuation: geom odd
-- statement:
--   The Two Adic Valuation construction uses the geom odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L24-L30

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

theorem Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.geom_odd (a : ℤ) (ha : Odd a) (n : ℕ) : (Odd (∑ i ∈ Finset.range n, a ^ i) ↔ Odd n) := by sorry
