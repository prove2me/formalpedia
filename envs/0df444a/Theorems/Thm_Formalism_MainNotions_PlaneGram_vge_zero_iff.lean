-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero_iff
-- name    : Formalism.MainNotions.PlaneGram.vge_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:49:19.572494+00:00
-- url     : https://prove2.me/theorems/306040b1-af4f-4321-9a62-046a85b4b8f6
-- title:
--   Plane Gram: vge zero iff
-- statement:
--   The Plane Gram construction uses the vge zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L33-L35

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

theorem Formalism.MainNotions.PlaneGram.vge_zero_iff (x : K) : vge v 0 x ↔ 0 ≤ v x := by sorry
