-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_two_pow_not_dvd
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_two_pow_not_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:06:14.533849+00:00
-- url     : https://prove2.me/theorems/a2ab504c-5397-4dc2-915c-f246f9e16f2d
-- title:
--   Two Adic Cyclotomic Decomposition: odd two pow not dvd
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd two pow not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L31-L33

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_two_pow_not_dvd (r n : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ∣ 2 ^ n := by sorry
