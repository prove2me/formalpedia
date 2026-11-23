-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_linMap_eq_sum
-- name    : Formalism.MainNotions.PlaneGram.linMap_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:05.451272+00:00
-- url     : https://prove2.me/theorems/f4c552e7-d97e-41a8-b4a5-a1a20e090985
-- title:
--   Plane Gram: lin Map eq sum
-- statement:
--   The Plane Gram construction uses the lin Map eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MlabNotMemYset.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MlabNotMemYset.lean#L14-L19

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MlabNotMemYset
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

theorem Formalism.MainNotions.PlaneGram.linMap_eq_sum {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K) (Y : MvPolynomial σ K) :
    T Y = ∑ ζ ∈ Y.support, Y.coeff ζ • T (monomial ζ 1) := by sorry
