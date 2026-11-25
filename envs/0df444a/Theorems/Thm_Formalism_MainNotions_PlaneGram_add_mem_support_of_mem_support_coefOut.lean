-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_add_mem_support_of_mem_support_coefOut
-- name    : Formalism.MainNotions.PlaneGram.add_mem_support_of_mem_support_coefOut
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:50:59.055544+00:00
-- url     : https://prove2.me/theorems/8f7dce6a-7ff2-462c-9281-1d5b241bbda0
-- title:
--   Plane Gram: add mem support of mem support coef Out
-- statement:
--   The Plane Gram construction uses the add mem support of mem support coef Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L442-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L442-L450

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

theorem Formalism.MainNotions.PlaneGram.add_mem_support_of_mem_support_coefOut {μ β : L × Fin r →₀ ℕ}
    {F : MvPolynomial (L × Fin r) K} (h : β ∈ (coefOut out μ F).support) : μ + β ∈ F.support := by sorry
