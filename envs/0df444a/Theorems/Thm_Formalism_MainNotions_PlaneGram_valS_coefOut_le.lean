-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_coefOut_le
-- name    : Formalism.MainNotions.PlaneGram.valS_coefOut_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:15.038701+00:00
-- url     : https://prove2.me/theorems/aebb48e6-8af8-40de-a6a8-f80a9e326b42
-- title:
--   Plane Gram: val S coef Out le
-- statement:
--   The Plane Gram construction uses the val S coef Out le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L472-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L472-L510

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
variable (sg : L → Bool) (S : Finset L)

theorem Formalism.MainNotions.PlaneGram.valS_coefOut_le (hout : ∀ i ∈ S, ¬ out i) (μ : L × Fin r →₀ ℕ)
    (F : MvPolynomial (L × Fin r) K) : valS sg S F ≤ valS sg S (coefOut out μ F) := by sorry
