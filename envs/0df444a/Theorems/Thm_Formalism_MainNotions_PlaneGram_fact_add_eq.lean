-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_add_eq
-- name    : Formalism.MainNotions.PlaneGram.fact_add_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:22.372666+00:00
-- url     : https://prove2.me/theorems/6f0fc4cd-a239-4389-919d-1a99f85b37af
-- title:
--   Plane Gram: fact add eq
-- statement:
--   The Plane Gram construction uses the fact add eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L357-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L357-L361

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

theorem Formalism.MainNotions.PlaneGram.fact_add_eq {σ : Type} [Fintype σ] (α α' : σ →₀ ℕ) :
    fact (α + α') = (∏ x, (α x + α' x).choose (α' x)) * fact α * fact α' := by sorry
