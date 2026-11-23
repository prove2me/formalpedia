-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_val_nonneg_of_pow_six
-- name    : Formalism.MainNotions.PlaneGram.val_nonneg_of_pow_six
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:23.89568+00:00
-- url     : https://prove2.me/theorems/3d0ea8a6-83f6-4558-8f4d-f35e3e38f344
-- title:
--   Plane Gram: val nonneg of pow six
-- statement:
--   The Plane Gram construction uses the val nonneg of pow six property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L40-L42

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

theorem Formalism.MainNotions.PlaneGram.val_nonneg_of_pow_six (x : K) (n : ℕ) (h : ((n : ℕ) : WithTop ℚ) ≤ v (x ^ 6)) : 0 ≤ v x := by sorry
