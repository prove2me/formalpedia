-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_conjE_mem_hostF_iff
-- name    : Formalism.FrobeniusOrbits.conjE_mem_hostF_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:26:28.334522+00:00
-- url     : https://prove2.me/theorems/256abef3-8eec-43f4-9b05-5bf4db3202aa
-- title:
--   Frobenius Orbits: conj E mem host F iff
-- statement:
--   The Frobenius Orbits construction uses the conj E mem host F iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L322-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L322-L330

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
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
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.conjE_mem_hostF_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (x : hostE ζ a b) : x ∈ hostF ζ a b ↔ conjE hqd h x = x := by sorry
