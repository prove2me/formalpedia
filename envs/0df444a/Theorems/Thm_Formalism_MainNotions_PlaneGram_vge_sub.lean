-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_sub
-- name    : Formalism.MainNotions.PlaneGram.vge_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:34.104196+00:00
-- url     : https://prove2.me/theorems/44d40e88-1809-4245-bdcd-54d4b0022c24
-- title:
--   Plane Gram: vge sub
-- statement:
--   The Plane Gram construction uses the vge sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L54-L56

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

theorem Formalism.MainNotions.PlaneGram.vge_sub {a : ℝ} {x y : K} (hx : vge v a x) (hy : vge v a y) : vge v a (x - y) := by sorry
