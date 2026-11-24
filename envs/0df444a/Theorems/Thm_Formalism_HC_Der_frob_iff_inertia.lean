-- Prove2me | Theorems.Thm_Formalism_HC_Der_frob_iff_inertia
-- name    : Formalism.HC.Der.frob_iff_inertia
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:13:08.060447+00:00
-- url     : https://prove2.me/theorems/e5e4b12c-50a3-4359-8e82-4feaebbd18be
-- title:
--   Der: frob iff inertia
-- statement:
--   The Der construction uses the frob iff inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L104-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean#L104-L116

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

theorem Formalism.HC.Der.frob_iff_inertia {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] [SMulCommClass G ℤ S]
    (P : Ideal S) (F σ : G) (hF : IsArithFrobAt ℤ F P) :
    IsArithFrobAt ℤ σ P ↔ ∀ x : S, (σ * F⁻¹) • x - x ∈ P := by sorry
