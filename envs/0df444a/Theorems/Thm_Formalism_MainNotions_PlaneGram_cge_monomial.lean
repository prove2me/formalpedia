-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_monomial
-- name    : Formalism.MainNotions.PlaneGram.cge_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:40.981823+00:00
-- url     : https://prove2.me/theorems/d4bc7d56-4d35-4181-834b-2881ae998738
-- title:
--   Plane Gram: cge monomial
-- statement:
--   The Plane Gram construction uses the cge monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L124-L131

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

theorem Formalism.MainNotions.PlaneGram.cge_monomial {σ : Type} {a : ℝ} {c : K} (α : σ →₀ ℕ) (hc : vge v a c) :
    cge v a (monomial α c) := by sorry
