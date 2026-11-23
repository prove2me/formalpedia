-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_exists_of_mem_support_lin
-- name    : Formalism.MainNotions.PlaneGram.exists_of_mem_support_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:31.224511+00:00
-- url     : https://prove2.me/theorems/f3b98039-ed9b-45a6-9d00-e4ba0c3d70a6
-- title:
--   Plane Gram: exists of mem support lin
-- statement:
--   The Plane Gram construction uses the exists of mem support lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L19-L30

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

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
variable {K : Type} [Field K]

theorem Formalism.MainNotions.PlaneGram.exists_of_mem_support_lin {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K)
    (Z : MvPolynomial σ K) {ζ' : τ →₀ ℕ} (h : ζ' ∈ (T Z).support) :
    ∃ ζ ∈ Z.support, ζ' ∈ (T (monomial ζ 1)).support := by sorry
