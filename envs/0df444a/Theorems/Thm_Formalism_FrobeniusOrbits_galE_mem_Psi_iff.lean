-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_galE_mem_Psi_iff
-- name    : Formalism.FrobeniusOrbits.galE_mem_Psi_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:22:43.033987+00:00
-- url     : https://prove2.me/theorems/45b369d5-d917-4eca-ba68-9ba5595d7993
-- title:
--   Frobenius Orbits: gal E mem Psi iff
-- statement:
--   The Frobenius Orbits construction uses the gal E mem Psi iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L68-L72

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
variable {e : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.galE_mem_Psi_iff (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    galE e ζ a b σ ∈ Psi e ↔ σ (bE ζ a b) = bE ζ a b := by sorry
