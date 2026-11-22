-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_gcd_two_pow
-- name    : Formalism.TwoAdicCyclotomicDecomposition.gcd_two_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:06:16.252407+00:00
-- url     : https://prove2.me/theorems/d079cfe1-3a44-4de1-8405-920c2b454751
-- title:
--   Two Adic Cyclotomic Decomposition: gcd two pow
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the gcd two pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NormalOrderTwoCentral.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NormalOrderTwoCentral.lean#L57-L71

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.gcd_two_pow (N k : ℕ) (hk : k ≠ 0) : Nat.gcd (2 ^ N) k = 2 ^ min N (padicValNat 2 k) := by sorry
