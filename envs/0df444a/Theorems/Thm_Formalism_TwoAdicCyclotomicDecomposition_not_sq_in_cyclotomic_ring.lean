-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_not_sq_in_cyclotomic_ring
-- name    : Formalism.TwoAdicCyclotomicDecomposition.not_sq_in_cyclotomic_ring
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:42.063737+00:00
-- url     : https://prove2.me/theorems/1c830352-750f-41e0-9308-7ffc401fcb53
-- title:
--   Two Adic Cyclotomic Decomposition: not sq in cyclotomic ring
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the not sq in cyclotomic ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L10-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L10-L52

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.not_sq_in_cyclotomic_ring (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (p : ℕ) [hp : Fact p.Prime] (hpN : ¬ p ∣ N)
    (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) (X : 𝓞 K) (hX : X ^ 2 = ((p * m : ℤ) : 𝓞 K)) : False := by sorry
