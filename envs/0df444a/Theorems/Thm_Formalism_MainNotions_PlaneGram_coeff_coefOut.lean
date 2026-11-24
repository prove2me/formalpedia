-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_coefOut
-- name    : Formalism.MainNotions.PlaneGram.coeff_coefOut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:47.996304+00:00
-- url     : https://prove2.me/theorems/32f96b1a-85b6-4f09-b12e-6e045963eedb
-- title:
--   Plane Gram: coeff coef Out
-- statement:
--   The Plane Gram construction uses the coeff coef Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L407-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L407-L434

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

theorem Formalism.MainNotions.PlaneGram.coeff_coefOut (μ β : L × Fin r →₀ ℕ) (F : MvPolynomial (L × Fin r) K) :
    (coefOut out μ F).coeff β =
      if eOut out β = 0 ∧ eOut out μ = μ then F.coeff (μ + β) else 0 := by sorry
