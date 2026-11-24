-- Prove2me | Theorems.Thm_Formalism_HC_Der_gal_eq_art_iff
-- name    : Formalism.HC.Der.gal_eq_art_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:54:08.047396+00:00
-- url     : https://prove2.me/theorems/4af25d2f-a89e-4de5-8313-377d290bc244
-- title:
--   Der: gal eq art iff
-- statement:
--   The Der construction uses the gal eq art iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycBasic.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycBasic.lean#L78-L86

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb

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

theorem Formalism.HC.Der.gal_eq_art_iff (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ) :
    H.gal σ = H.art u ↔ ∀ x, emb H (σ x) = tauN H.condN u (emb H x) := by sorry
