-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_galE_of_lift
-- name    : Formalism.FrobeniusOrbits.galE_of_lift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:24:01.635912+00:00
-- url     : https://prove2.me/theorems/82afaf08-35c6-42e1-b892-a9b8d08ad07c
-- title:
--   Frobenius Orbits: gal E of lift
-- statement:
--   The Frobenius Orbits construction uses the gal E of lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L179-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L179-L205

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

theorem Formalism.FrobeniusOrbits.galE_of_lift (h : IsLayer (e + 2) q d ζ a b) {σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b}
    {τ : L ≃ₐ[ℚ] L} (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) :
    galE e ζ a b σ =
      (((galMap h.1 a b τ).2.1, (galMap h.1 a b τ).2.2), hcl e (galMap h.1 a b τ).1) := by sorry
