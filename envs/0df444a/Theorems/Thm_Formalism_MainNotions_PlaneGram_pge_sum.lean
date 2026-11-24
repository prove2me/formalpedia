-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_sum
-- name    : Formalism.MainNotions.PlaneGram.pge_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:07:51.318973+00:00
-- url     : https://prove2.me/theorems/0f0fc29d-74b6-4d24-873a-d3c98bd25dde
-- title:
--   Plane Gram: pge sum
-- statement:
--   The Plane Gram construction uses the pge sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L82-L85

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
variable {R : Type} [CommSemiring R] {σ : Type}

theorem Formalism.MainNotions.PlaneGram.pge_sum {ι : Type} {n : WithTop ℤ} (s : Finset ι)
    (f : ι → MvPolynomial σ (LaurentPolynomial R)) (h : ∀ i ∈ s, pge n (f i)) :
    pge n (∑ i ∈ s, f i) := by sorry
