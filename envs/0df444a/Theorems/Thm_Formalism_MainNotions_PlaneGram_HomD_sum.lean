-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_sum
-- name    : Formalism.MainNotions.PlaneGram.HomD_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:02:58.380603+00:00
-- url     : https://prove2.me/theorems/3abb68e2-2bf2-4dc2-ba5c-251877f08566
-- title:
--   Plane Gram: Hom D sum
-- statement:
--   The Plane Gram construction uses the Hom D sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L704-L709
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L704-L709

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

theorem Formalism.MainNotions.PlaneGram.HomD_sum {ι : Type} {d : L → ℕ} (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) R)
    (h : ∀ k ∈ s, HomD d (f k)) : HomD d (∑ k ∈ s, f k) := by sorry
