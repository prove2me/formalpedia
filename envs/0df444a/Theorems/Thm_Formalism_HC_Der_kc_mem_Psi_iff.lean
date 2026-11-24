-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_mem_Psi_iff
-- name    : Formalism.HC.Der.kc_mem_Psi_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:50:05.879661+00:00
-- url     : https://prove2.me/theorems/b4571ad2-057a-49fd-ad00-02cf06f5602f
-- title:
--   Der: kc mem Psi iff
-- statement:
--   The Der construction uses the kc mem Psi iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcBase.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcBase.lean#L29-L44

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

theorem Formalism.HC.Der.kc_mem_Psi_iff (σ : H.E ≃ₐ[ℚ] H.E) : H.gal σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by sorry
