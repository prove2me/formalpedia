-- Prove2me | Theorems.Thm_Formalism_HC_Der_mem_over_iff
-- name    : Formalism.HC.Der.mem_over_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:13:42.853845+00:00
-- url     : https://prove2.me/theorems/7fcbe35a-3788-4041-bffb-ad14a6b0edc9
-- title:
--   Der: mem over iff
-- statement:
--   The Der construction uses the mem over iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L23-L25

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
omit [IsScalarTower ℚ E L] [NumberField E] [NumberField L]

theorem Formalism.HC.Der.mem_over_iff (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.LiesOver P] (x : 𝓞 E) :
    x ∈ P ↔ algebraMap (𝓞 E) (𝓞 L) x ∈ Q := by sorry
