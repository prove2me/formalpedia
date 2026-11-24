-- Prove2me | Theorems.Thm_Formalism_HC_Der_smul_mem_of_inertia
-- name    : Formalism.HC.Der.smul_mem_of_inertia
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:13:16.125945+00:00
-- url     : https://prove2.me/theorems/06f7c68b-c9a8-4a09-9033-a868d05a1ff0
-- title:
--   Der: smul mem of inertia
-- statement:
--   The Der construction uses the smul mem of inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L46-L48

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

theorem Formalism.HC.Der.smul_mem_of_inertia {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G) (I : Ideal S)
    (h : ∀ x : S, g • x - x ∈ I) (z : S) : g • z ∈ I ↔ z ∈ I := by sorry
