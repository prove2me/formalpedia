-- Prove2me | Theorems.Thm_Formalism_HC_Der_res_smul
-- name    : Formalism.HC.Der.res_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:13:02.158499+00:00
-- url     : https://prove2.me/theorems/fbff26fb-f22b-4018-9f7b-d97267cba049
-- title:
--   Der: res smul
-- statement:
--   The Der construction uses the res smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L17-L20

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
omit [IsScalarTower ℚ E L]

theorem Formalism.HC.Der.res_smul (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L) (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) (x : 𝓞 E) :
    algebraMap (𝓞 E) (𝓞 L) (σ • x) = τ • algebraMap (𝓞 E) (𝓞 L) x := by sorry
