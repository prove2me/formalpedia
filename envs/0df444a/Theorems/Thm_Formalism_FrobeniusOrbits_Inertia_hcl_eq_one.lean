-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_hcl_eq_one
-- name    : Formalism.FrobeniusOrbits.Inertia.hcl_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:11:15.239852+00:00
-- url     : https://prove2.me/theorems/e26379ab-8f52-4a92-992d-3bb3268baf0a
-- title:
--   Inertia: hcl eq one
-- statement:
--   The Inertia construction uses the hcl eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L119-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L119-L210

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

theorem Formalism.FrobeniusOrbits.Inertia.hcl_eq_one (h : IsLayer (e + 2) q d ζ a b) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (τ : Gal(L/ℚ)) (Θ : 𝓞 L)
    (hΘ : (Θ : L) = ζ + ζ⁻¹) (hmem : τ • Θ - Θ ∈ Q) : hcl e (h.1.autToPow ℚ τ) = 1 := by sorry
