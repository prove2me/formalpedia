-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_coefOut_sum
-- name    : Formalism.MainNotions.PlaneGram.coefOut_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:04.934304+00:00
-- url     : https://prove2.me/theorems/d2ed6839-5594-4c29-8a98-2a6c0a5d7e24
-- title:
--   Plane Gram: coef Out sum
-- statement:
--   The Plane Gram construction uses the coef Out sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L397-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L397-L400

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]

theorem Formalism.MainNotions.PlaneGram.coefOut_sum {ι : Type} (μ : L × Fin r →₀ ℕ) (s : Finset ι)
    (f : ι → MvPolynomial (L × Fin r) K) :
    coefOut out μ (∑ i ∈ s, f i) = ∑ i ∈ s, coefOut out μ (f i) := by sorry
