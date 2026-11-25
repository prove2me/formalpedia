-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_hPart_inertia
-- name    : Formalism.FrobeniusOrbits.Decomp.hPart_inertia
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:11:32.222801+00:00
-- url     : https://prove2.me/theorems/a48c8a21-a495-4567-8a06-d29d299d9cb1
-- title:
--   Decomp: h Part inertia
-- statement:
--   The Decomp construction uses the h Part inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L156-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L156-L287

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Decomp
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Decomp.hPart_inertia (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (P : Ideal (𝓞 (hostE ζ a b))) [Q.LiesOver P] (ρ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hρ : ∀ x : 𝓞 (hostE ζ a b), ρ • x - x ∈ P) : (galE e ζ a b ρ).2 = 1 := by sorry
