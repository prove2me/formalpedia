-- Prove2me | Theorems.Thm_Formalism_HC_Frame_hostThickOrbitH
-- name    : Formalism.HC.Frame.hostThickOrbitH
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:08.495469+00:00
-- url     : https://prove2.me/theorems/53d0e906-df71-551b-8335-698d03de5c0b
-- title:
--   Frame: host Thick Orbit H
-- statement:
--   The Frame construction uses the host Thick Orbit H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L832-L839
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L832-L839

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
open Classical

theorem Formalism.HC.Frame.hostThickOrbitH {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0) (hR : NoRel T L)
    (u₀ t x : φ.A) :
    (4 * L < addOrderOf (φ.h x) → ∀ i₀ : ℤ,
      ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => φ.InTranslate T u₀ (t + i • x))).card ≤ 2) ∧
    (addOrderOf (φ.h x) ≤ 4 * L →
      {y : φ.A | (∃ i : ℤ, y = t + i • x) ∧ φ.InTranslate T u₀ y}.ncard ≤ 1) := by sorry
