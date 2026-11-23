-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_sum_coefOut
-- name    : Formalism.MainNotions.PlaneGram.sum_coefOut
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:56.250113+00:00
-- url     : https://prove2.me/theorems/c3e314ff-721b-430a-9a6f-ae0e09043e91
-- title:
--   Plane Gram: sum coef Out
-- statement:
--   The Plane Gram construction uses the sum coef Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L463-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L463-L468

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

theorem Formalism.MainNotions.PlaneGram.sum_coefOut (F : MvPolynomial (L × Fin r) K) :
    F = ∑ μ ∈ F.support.image (eOut out), monomial μ 1 * coefOut out μ F := by sorry
