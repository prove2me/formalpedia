-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_sup
-- name    : Formalism.FrobeniusOrbits.Inertia.sup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:11:05.324531+00:00
-- url     : https://prove2.me/theorems/6778e289-3d77-4272-b401-86e68f858abf
-- title:
--   Inertia: sup
-- statement:
--   The Inertia construction uses the sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L258-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L258-L311

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

theorem Formalism.FrobeniusOrbits.Inertia.sup (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (g : GalL (e + 2))
    (hg : galE e ζ a b σ = ((g.2.1, g.2.2), hcl e g.1))
    (hI : ∀ τ : Gal(L/ℚ), galMap h.1 a b τ = g → ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime]
      [Q.LiesOver (span {(p : ℤ)})], ∀ y : 𝓞 L, τ • y - y ∈ Q) :
    ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P := by sorry
