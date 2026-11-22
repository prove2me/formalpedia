-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_natCast_bound
-- name    : Formalism.MainNotions.PlaneGram.vge_natCast_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:36.184842+00:00
-- url     : https://prove2.me/theorems/2c77595a-4a6b-475b-86d1-8a263060089d
-- title:
--   Plane Gram: vge nat Cast bound
-- statement:
--   The Plane Gram construction uses the vge nat Cast bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L37-L39

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

theorem Formalism.MainNotions.PlaneGram.vge_natCast_bound (c : ℕ) (x : K) : vge v (c : ℝ) x ↔ ((c : ℕ) : WithTop ℚ) ≤ v x := by sorry
