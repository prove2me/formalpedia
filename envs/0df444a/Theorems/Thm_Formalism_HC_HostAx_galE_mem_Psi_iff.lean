-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_galE_mem_Psi_iff
-- name    : Formalism.HC.HostAx.galE_mem_Psi_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:10.861357+00:00
-- url     : https://prove2.me/theorems/a1ce9a9a-041d-405c-b2e3-e68e175d2d0a
-- title:
--   Host Ax: gal E mem Psi iff
-- statement:
--   The Host Ax construction uses the gal E mem Psi iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean#L209-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean#L209-L224

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

theorem Formalism.HC.HostAx.galE_mem_Psi_iff (σ : H.E ≃ₐ[ℚ] H.E) : H.galE σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by sorry
