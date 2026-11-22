-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_sum
-- name    : Formalism.MainNotions.PlaneGram.cge_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:53.246954+00:00
-- url     : https://prove2.me/theorems/79612c33-680c-4dec-9de2-bfab2a90f8e1
-- title:
--   Plane Gram: cge sum
-- statement:
--   The Plane Gram construction uses the cge sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L112-L116

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

theorem Formalism.MainNotions.PlaneGram.cge_sum {σ ι : Type} {a : ℝ} (s : Finset ι) (f : ι → MvPolynomial σ K)
    (h : ∀ i ∈ s, cge v a (f i)) : cge v a (∑ i ∈ s, f i) := by sorry
