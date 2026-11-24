-- Prove2me | Theorems.Thm_Formalism_HC_Der_inertia_lift
-- name    : Formalism.HC.Der.inertia_lift
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:13:12.667456+00:00
-- url     : https://prove2.me/theorems/990899e3-cfa2-497e-bbd1-3024aec0786b
-- title:
--   Der: inertia lift
-- statement:
--   The Der construction uses the inertia lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L50-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L50-L87

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
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
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsScalarTower ℚ E L]

theorem Formalism.HC.Der.inertia_lift [IsGalois ℚ L] (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver P] (σ : E ≃ₐ[ℚ] E)
    (hσ : ∀ x : 𝓞 E, σ • x - x ∈ P) :
    ∃ τ : L ≃ₐ[ℚ] L, (∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) ∧ ∀ y : 𝓞 L, τ • y - y ∈ Q := by sorry
