-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_not_sq_cyc
-- name    : Formalism.TwoAdicCyclotomicDecomposition.not_sq_cyc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:28.282793+00:00
-- url     : https://prove2.me/theorems/def2ce19-ab8c-4b55-9775-515154a74eac
-- title:
--   Two Adic Cyclotomic Decomposition: not sq cyc
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the not sq cyc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean#L54-L62

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

theorem Formalism.TwoAdicCyclotomicDecomposition.not_sq_cyc (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) (x : K) (hx : x ^ 2 = ((p * m : ℤ) : K)) : False := by sorry
