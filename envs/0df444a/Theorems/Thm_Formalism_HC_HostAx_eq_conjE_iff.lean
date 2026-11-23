-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_eq_conjE_iff
-- name    : Formalism.HC.HostAx.eq_conjE_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:57.219956+00:00
-- url     : https://prove2.me/theorems/45fbcba6-0c64-437b-81d7-43d2df5c1ccf
-- title:
--   Host Ax: eq conj E iff
-- statement:
--   The Host Ax construction uses the eq conj E iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean#L194-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean#L194-L195

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

theorem Formalism.HC.HostAx.eq_conjE_iff (σ : H.E ≃ₐ[ℚ] H.E) : σ = H.conj ↔ H.galE σ = φ.cc := by sorry
