-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vle_mul
-- name    : Formalism.MainNotions.PlaneGram.vle_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:36.918484+00:00
-- url     : https://prove2.me/theorems/74bcbc59-0a68-4816-b84a-1d73123166f0
-- title:
--   Plane Gram: vle mul
-- statement:
--   The Plane Gram construction uses the vle mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L76-L79

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

theorem Formalism.MainNotions.PlaneGram.vle_mul {a b : ℝ} {x y : K} (hx : vle v a x) (hy : vle v b y) : vle v (a + b) (x * y) := by sorry
