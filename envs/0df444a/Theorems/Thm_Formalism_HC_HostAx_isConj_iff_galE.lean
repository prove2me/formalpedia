-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_isConj_iff_galE
-- name    : Formalism.HC.HostAx.isConj_iff_galE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:02.542218+00:00
-- url     : https://prove2.me/theorems/28cc321f-f342-44f3-9a23-90363c907257
-- title:
--   Host Ax: is Conj iff gal E
-- statement:
--   The Host Ax construction uses the is Conj iff gal E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean#L196-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean#L196-L197

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
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
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
attribute [instance] HostRaw.instField HostRaw.instNF
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)

theorem Formalism.HC.HostAx.isConj_iff_galE (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E) :
    (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.galE σ = φ.cc := by sorry
