-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_trace_eq_iff
-- name    : Formalism.FrobeniusOrbits.Galois.trace_eq_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:18.741855+00:00
-- url     : https://prove2.me/theorems/4bfca5fd-2732-4d88-a595-c9204598c1f3
-- title:
--   Galois: trace eq iff
-- statement:
--   The Galois construction uses the trace eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L37-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L37-L57

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}

theorem Formalism.FrobeniusOrbits.Galois.trace_eq_iff (hζ : IsPrimitiveRoot ζ N) (u c : ZMod N) :
    ζ ^ u.val + ζ⁻¹ ^ u.val = ζ ^ c.val + ζ⁻¹ ^ c.val ↔ u = c ∨ u = -c := by sorry
