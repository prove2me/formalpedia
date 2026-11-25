-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_coefOutL_apply
-- name    : Formalism.MainNotions.PlaneGram.coefOutL_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:07.984493+00:00
-- url     : https://prove2.me/theorems/a33a0aba-2ccc-4e63-9d9b-9df32a2f46de
-- title:
--   Plane Gram: coef Out L apply
-- statement:
--   The Plane Gram construction uses the coef Out L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L394-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L394-L395

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

theorem Formalism.MainNotions.PlaneGram.coefOutL_apply (μ : L × Fin r →₀ ℕ) (F : MvPolynomial (L × Fin r) K) :
    coefOutL out μ F = coefOut out μ F := by sorry
