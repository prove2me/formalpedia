-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_stab_of_inertia
-- name    : Formalism.HC.Der.kc_stab_of_inertia
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:50:18.965828+00:00
-- url     : https://prove2.me/theorems/847b0443-fc60-4ec8-a7a6-3e0599e569be
-- title:
--   Der: kc stab of inertia
-- statement:
--   The Der construction uses the kc stab of inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcBase.lean#L85-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcBase.lean#L85-L96

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.Der.kc_stab_of_inertia {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G) (P : Ideal S)
    (h : ∀ x : S, g • x - x ∈ P) : g ∈ MulAction.stabilizer G P := by sorry
