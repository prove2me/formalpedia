-- Prove2me | Theorems.Thm_Formalism_HC_Der_exists_over
-- name    : Formalism.HC.Der.exists_over
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:13:35.897781+00:00
-- url     : https://prove2.me/theorems/ebfd6334-c52b-48e8-9afd-9b951dc13eca
-- title:
--   Der: exists over
-- statement:
--   The Der construction uses the exists over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L91-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L91-L102

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

theorem Formalism.HC.Der.exists_over {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [IsGalois ℚ L] (ι : E →ₐ[ℚ] L)
    (l : ℕ) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (span {(l : ℤ)})),
      (∀ (σ : E ≃ₐ[ℚ] E), (∀ x : 𝓞 E, σ • x - x ∈ P) ↔
        ∃ τ : L ≃ₐ[ℚ] L, (∀ x, ι (σ x) = τ (ι x)) ∧ ∀ y : 𝓞 L, τ • y - y ∈ Q) ∧
      ∀ (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L), (∀ x, ι (σ x) = τ (ι x)) → IsArithFrobAt ℤ τ Q → IsArithFrobAt ℤ σ P := by sorry
