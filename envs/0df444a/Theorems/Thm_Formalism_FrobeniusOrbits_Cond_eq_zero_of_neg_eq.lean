-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_eq_zero_of_neg_eq
-- name    : Formalism.FrobeniusOrbits.Cond.eq_zero_of_neg_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:10:43.425299+00:00
-- url     : https://prove2.me/theorems/a30ae709-98c5-4d6a-8219-c575da6c2e09
-- title:
--   Cond: eq zero of neg eq
-- statement:
--   The Cond construction uses the eq zero of neg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L204-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L204-L208

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond

theorem Formalism.FrobeniusOrbits.Cond.eq_zero_of_neg_eq {K : Type*} [Field K] [CharZero K] {g : K} (h : -g = g) : g = 0 := by sorry
