-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_mul
-- name    : Formalism.MainNotions.PlaneGram.dg_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:22.7861+00:00
-- url     : https://prove2.me/theorems/9b79fb62-6217-4791-bf53-5e24f4c951aa
-- title:
--   Plane Gram: dg mul
-- statement:
--   The Plane Gram construction uses the dg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1139-L1141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1139-L1141

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
variable {K : Type} [Field K]

theorem Formalism.MainNotions.PlaneGram.dg_mul {σ : Type} (f g : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg (fun α => f α * g α) F = dg f (dg g F) := by sorry
