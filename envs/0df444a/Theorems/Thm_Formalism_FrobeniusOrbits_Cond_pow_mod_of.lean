-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_pow_mod_of
-- name    : Formalism.FrobeniusOrbits.Cond.pow_mod_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:10:31.859877+00:00
-- url     : https://prove2.me/theorems/9f9dcb47-c247-4464-a7c8-313a04502229
-- title:
--   Cond: pow mod of
-- statement:
--   The Cond construction uses the pow mod of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L106-L108

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

theorem Formalism.FrobeniusOrbits.Cond.pow_mod_of {K : Type*} [Monoid K] {w : K} {N : ℕ} (hw : w ^ N = 1) (a : ℕ) :
    w ^ (a % N) = w ^ a := by sorry
