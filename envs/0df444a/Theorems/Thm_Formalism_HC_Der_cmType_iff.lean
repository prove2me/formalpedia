-- Prove2me | Theorems.Thm_Formalism_HC_Der_cmType_iff
-- name    : Formalism.HC.Der.cmType_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:01:13.209277+00:00
-- url     : https://prove2.me/theorems/771d71b2-1191-4196-9e5f-b9a704f165ae
-- title:
--   Der: cm Type iff
-- statement:
--   The Der construction uses the cm Type iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycAll.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycAll.lean#L25-L34

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_cmType

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
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.Der.cmType_iff (ψ : H.E →+* ℂ) : ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType := by sorry
