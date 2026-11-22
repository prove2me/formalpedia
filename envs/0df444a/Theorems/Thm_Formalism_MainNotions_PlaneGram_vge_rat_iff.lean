-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_rat_iff
-- name    : Formalism.MainNotions.PlaneGram.vge_rat_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:21.704688+00:00
-- url     : https://prove2.me/theorems/b6006ccc-2b53-4485-9ca8-2e3f8ae431ac
-- title:
--   Plane Gram: vge rat iff
-- statement:
--   The Plane Gram construction uses the vge rat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L29-L31

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

theorem Formalism.MainNotions.PlaneGram.vge_rat_iff (n : ℚ) (x : K) : vge v (n : ℝ) x ↔ (n : WithTop ℚ) ≤ v x := by sorry
