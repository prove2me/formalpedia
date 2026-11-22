-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_ne_zero
-- name    : Formalism.MainNotions.PlaneGram.fact_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:15:46.841476+00:00
-- url     : https://prove2.me/theorems/eb073385-d9fc-444f-b664-a8f65fc610ce
-- title:
--   Plane Gram: fact ne zero
-- statement:
--   The Plane Gram construction uses the fact ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L313-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L313-L315

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))

theorem Formalism.MainNotions.PlaneGram.fact_ne_zero {σ : Type} (α : σ →₀ ℕ) : fact α ≠ 0 := by sorry
