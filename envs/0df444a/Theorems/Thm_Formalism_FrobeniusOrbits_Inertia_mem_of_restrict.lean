-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_mem_of_restrict
-- name    : Formalism.FrobeniusOrbits.Inertia.mem_of_restrict
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:11:45.635808+00:00
-- url     : https://prove2.me/theorems/909b8dac-7d18-47af-9da6-227c150f4d4e
-- title:
--   Inertia: mem of restrict
-- statement:
--   The Inertia construction uses the mem of restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L99-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L99-L107

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Inertia.mem_of_restrict (P : Ideal (𝓞 (hostE ζ a b))) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x)
    (hτ : ∀ y : 𝓞 L, τ • y - y ∈ Q) : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P := by sorry
