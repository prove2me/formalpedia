-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_natLog_le_term
-- name    : Formalism.MainNotions.PlaneGram.natLog_le_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:35.796066+00:00
-- url     : https://prove2.me/theorems/6e2d4e50-ba0c-4a44-9058-86695e86b9c8
-- title:
--   Plane Gram: nat Log le term
-- statement:
--   The Plane Gram construction uses the nat Log le term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L428-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L428-L440

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

theorem Formalism.MainNotions.PlaneGram.natLog_le_term {p : ℕ} (hp : 2 ≤ p) (r a : ℕ) :
    (r : ℝ) * (Nat.log p a : ℝ) ≤ (if a = 0 then 0 else (r : ℝ) * Real.logb p ((a : ℝ) + r)) := by sorry
