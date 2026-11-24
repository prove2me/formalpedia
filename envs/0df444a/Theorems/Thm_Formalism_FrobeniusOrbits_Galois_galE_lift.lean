-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galE_lift
-- name    : Formalism.FrobeniusOrbits.Galois.galE_lift
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:53:20.668585+00:00
-- url     : https://prove2.me/theorems/889dd9b4-5f91-4b9b-9f74-678b2d40f439
-- title:
--   Galois: gal E lift
-- statement:
--   The Galois construction uses the gal E lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L327-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L327-L332

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
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Galois.galE_lift (h : IsLayer (e + 2) q d ζ a b) {σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b}
    {τ : Gal(L/ℚ)} (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) :
    galE e ζ a b σ =
      (((galMap h.1 a b τ).2.1, (galMap h.1 a b τ).2.2), hcl e (galMap h.1 a b τ).1) := by sorry
