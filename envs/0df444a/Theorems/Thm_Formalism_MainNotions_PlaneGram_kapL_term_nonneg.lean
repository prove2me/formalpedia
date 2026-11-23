-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_kapL_term_nonneg
-- name    : Formalism.MainNotions.PlaneGram.kapL_term_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:39.413744+00:00
-- url     : https://prove2.me/theorems/57632572-23d2-40be-aa49-98b15b7072f2
-- title:
--   Plane Gram: kap L term nonneg
-- statement:
--   The Plane Gram construction uses the kap L term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L381-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L381-L385

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

theorem Formalism.MainNotions.PlaneGram.kapL_term_nonneg {p : ℕ} (hp : 2 ≤ p) (r a : ℕ) :
    0 ≤ (if a = 0 then 0 else (r : ℝ) * Real.logb p ((a : ℝ) + r)) := by sorry
