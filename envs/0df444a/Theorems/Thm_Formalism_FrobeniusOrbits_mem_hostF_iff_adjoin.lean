-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_mem_hostF_iff_adjoin
-- name    : Formalism.FrobeniusOrbits.mem_hostF_iff_adjoin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:22:53.60634+00:00
-- url     : https://prove2.me/theorems/d1b26ccd-5732-4da0-886e-1b7bc459d18c
-- title:
--   Frobenius Orbits: mem host F iff adjoin
-- statement:
--   The Frobenius Orbits construction uses the mem host F iff adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L332-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L332-L333

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

theorem Formalism.FrobeniusOrbits.mem_hostF_iff_adjoin (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (x : hostE ζ a b) : x ∈ hostF ζ a b ↔ (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯ := by sorry
