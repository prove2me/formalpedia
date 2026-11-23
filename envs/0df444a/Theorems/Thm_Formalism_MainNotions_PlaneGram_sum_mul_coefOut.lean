-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_sum_mul_coefOut
-- name    : Formalism.MainNotions.PlaneGram.sum_mul_coefOut
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:44.310134+00:00
-- url     : https://prove2.me/theorems/304fdc91-aec8-4954-83b3-a9913a164c87
-- title:
--   Plane Gram: sum mul coef Out
-- statement:
--   The Plane Gram construction uses the sum mul coef Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L452-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L452-L461

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

theorem Formalism.MainNotions.PlaneGram.sum_mul_coefOut (g : (L × Fin r →₀ ℕ) → MvPolynomial (L × Fin r) K)
    (F : MvPolynomial (L × Fin r) K) :
    ∑ μ ∈ F.support.image (eOut out), g μ * coefOut out μ F =
      ∑ α ∈ F.support, g (eOut out α) * monomial (eIn out α) (F.coeff α) := by sorry
