-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_congr
-- name    : Formalism.MainNotions.PlaneGram.dg_congr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:06:21.575194+00:00
-- url     : https://prove2.me/theorems/e8cab197-4c0a-442a-8e8e-ab141012db33
-- title:
--   Plane Gram: dg congr
-- statement:
--   The Plane Gram construction uses the dg congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1152-L1158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1152-L1158

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

theorem Formalism.MainNotions.PlaneGram.dg_congr {σ : Type} {f g : (σ →₀ ℕ) → K} {F : MvPolynomial σ K}
    (h : ∀ α ∈ F.support, f α = g α) : dg f F = dg g F := by sorry
