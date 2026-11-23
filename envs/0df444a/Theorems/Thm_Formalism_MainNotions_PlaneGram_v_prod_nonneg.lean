-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_v_prod_nonneg
-- name    : Formalism.MainNotions.PlaneGram.v_prod_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:13.646346+00:00
-- url     : https://prove2.me/theorems/ef6a96b5-0999-4ce9-90dd-ee985239fb3a
-- title:
--   Plane Gram: v prod nonneg
-- statement:
--   The Plane Gram construction uses the v prod nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L65-L73

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}

theorem Formalism.MainNotions.PlaneGram.v_prod_nonneg {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, 0 ≤ v (f i)) :
    0 ≤ v (∏ i ∈ s, f i) := by sorry
