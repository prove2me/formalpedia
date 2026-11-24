-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_eq_zero_of_mem_support_coefOut
-- name    : Formalism.MainNotions.PlaneGram.eOut_eq_zero_of_mem_support_coefOut
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:06:17.8122+00:00
-- url     : https://prove2.me/theorems/3d4b19d4-3525-455c-9eb2-d594af9eea3f
-- title:
--   Plane Gram: e Out eq zero of mem support coef Out
-- statement:
--   The Plane Gram construction uses the e Out eq zero of mem support coef Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L436-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L436-L440

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

theorem Formalism.MainNotions.PlaneGram.eOut_eq_zero_of_mem_support_coefOut {μ β : L × Fin r →₀ ℕ} {F : MvPolynomial (L × Fin r) K}
    (h : β ∈ (coefOut out μ F).support) : eOut out β = 0 := by sorry
