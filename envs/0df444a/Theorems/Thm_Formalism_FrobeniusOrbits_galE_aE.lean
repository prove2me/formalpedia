-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_galE_aE
-- name    : Formalism.FrobeniusOrbits.galE_aE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:24:18.725794+00:00
-- url     : https://prove2.me/theorems/aaa586e8-3584-4ac8-b135-87eeecbba9ec
-- title:
--   Frobenius Orbits: gal E a E
-- statement:
--   The Frobenius Orbits construction uses the gal E a E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L207-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L207-L227

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

theorem Formalism.FrobeniusOrbits.galE_aE (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    ((σ (aE ζ a b) : hostE ζ a b) : L) = ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) : L) * a := by sorry
