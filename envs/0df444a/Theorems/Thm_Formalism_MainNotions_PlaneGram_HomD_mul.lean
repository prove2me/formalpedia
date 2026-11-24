-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_mul
-- name    : Formalism.MainNotions.PlaneGram.HomD_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:03:14.061811+00:00
-- url     : https://prove2.me/theorems/1a2512ff-2f69-4343-8b84-a81686284935
-- title:
--   Plane Gram: Hom D mul
-- statement:
--   The Plane Gram construction uses the Hom D mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L697-L702
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L697-L702

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {L : Type} {r : ℕ}
variable {R : Type} [CommSemiring R]

theorem Formalism.MainNotions.PlaneGram.HomD_mul {d d' : L → ℕ} {G G' : MvPolynomial (L × Fin r) R} (hG : HomD d G)
    (hG' : HomD d' G') : HomD (fun i => d i + d' i) (G * G') := by sorry
