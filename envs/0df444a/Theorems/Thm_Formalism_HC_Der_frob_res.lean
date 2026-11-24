-- Prove2me | Theorems.Thm_Formalism_HC_Der_frob_res
-- name    : Formalism.HC.Der.frob_res
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:13:53.274079+00:00
-- url     : https://prove2.me/theorems/3cd8cbad-80c8-43b2-ad5e-ea2daf1c02d3
-- title:
--   Der: frob res
-- statement:
--   The Der construction uses the frob res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L35-L44

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

theorem Formalism.HC.Der.frob_res (p : ℕ) (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.LiesOver P] [Q.LiesOver (span {(p : ℤ)})]
    [P.LiesOver (span {(p : ℤ)})] (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L)
    (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) (hτ : IsArithFrobAt ℤ τ Q) : IsArithFrobAt ℤ σ P := by sorry
