-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_isConj_iff_galE
-- name    : Formalism.FrobeniusOrbits.isConj_iff_galE
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:23:32.787024+00:00
-- url     : https://prove2.me/theorems/43f806f7-489b-4918-95ab-0c9876172484
-- title:
--   Frobenius Orbits: is Conj iff gal E
-- statement:
--   The Frobenius Orbits construction uses the is Conj iff gal E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L297-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/RealSubfieldLeCompositum.lean#L297-L305

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

theorem Formalism.FrobeniusOrbits.isConj_iff_galE (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (φ : hostE ζ a b →+* ℂ) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galE e ζ a b σ = cc e := by sorry
