-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_hostReal_at
-- name    : Formalism.FrobeniusOrbits.hostReal_at
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:27:23.700282+00:00
-- url     : https://prove2.me/theorems/9c62ed39-37a4-4179-b0b1-a361fad4a514
-- title:
--   Frobenius Orbits: host Real at
-- statement:
--   The Frobenius Orbits construction uses the host Real at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L311-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L311-L317

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

theorem Formalism.FrobeniusOrbits.hostReal_at (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    Module.finrank ℚ (hostF ζ a b) = 2 ^ (e + 1) ∧
    ∀ x : hostE ζ a b,
      (x ∈ hostF ζ a b ↔
        ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e → σ x = x) ∧
      (x ∈ hostF ζ a b ↔ (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯) := by sorry
