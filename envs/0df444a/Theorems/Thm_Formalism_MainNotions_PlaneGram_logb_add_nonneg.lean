-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_logb_add_nonneg
-- name    : Formalism.MainNotions.PlaneGram.logb_add_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:00.28306+00:00
-- url     : https://prove2.me/theorems/cec0d958-d279-4257-8a30-e2da88be64a2
-- title:
--   Plane Gram: logb add nonneg
-- statement:
--   The Plane Gram construction uses the logb add nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L366-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L366-L370

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

theorem Formalism.MainNotions.PlaneGram.logb_add_nonneg {p : ℕ} (hp : 2 ≤ p) (r a : ℕ) (h : 1 ≤ a + r) :
    0 ≤ Real.logb p ((a : ℝ) + r) := by sorry
