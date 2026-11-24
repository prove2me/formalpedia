-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_prim_pow
-- name    : Formalism.FrobeniusOrbits.Cond.prim_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:10:31.486814+00:00
-- url     : https://prove2.me/theorems/4adece07-48cc-4858-968b-432538cbd4a4
-- title:
--   Cond: prim pow
-- statement:
--   The Cond construction uses the prim pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L143-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L143-L145

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

theorem Formalism.FrobeniusOrbits.Cond.prim_pow {N m : ℕ} [NeZero N] (hm : m ∣ N) : IsPrimitiveRoot (z N ^ (N / m)) m := by sorry
