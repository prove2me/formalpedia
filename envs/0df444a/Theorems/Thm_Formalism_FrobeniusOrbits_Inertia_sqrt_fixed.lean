-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_sqrt_fixed
-- name    : Formalism.FrobeniusOrbits.Inertia.sqrt_fixed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:10:36.786099+00:00
-- url     : https://prove2.me/theorems/3f0ce8b7-30f2-4f01-a795-9da9c1a7d347
-- title:
--   Inertia: sqrt fixed
-- statement:
--   The Inertia construction uses the sqrt fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L53-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L53-L79

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

theorem Formalism.FrobeniusOrbits.Inertia.sqrt_fixed {F : Type} [Field F] [NumberField F] {r p : ℕ} (hr : r.Prime) (hr4 : r % 4 = 3)
    (hp : p.Prime) (hpr : p ≠ r) (P : Ideal (𝓞 F)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : F ≃ₐ[ℚ] F) {X : F} (hX : X ^ 2 = -(r : F)) (hσX : σ X = -X) :
    ¬ ∀ y : 𝓞 F, σ • y - y ∈ P := by sorry
