-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_le_val_of_le_pow_six
-- name    : Formalism.MainNotions.PlaneGram.le_val_of_le_pow_six
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:30.032963+00:00
-- url     : https://prove2.me/theorems/4863bee4-0eec-464c-9f0b-c98e7828c5d6
-- title:
--   Plane Gram: le val of le pow six
-- statement:
--   The Plane Gram construction uses the le val of le pow six property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L25-L38

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

theorem Formalism.MainNotions.PlaneGram.le_val_of_le_pow_six (x : K) (m n : ℕ) (hmn : 6 * m ≤ n)
    (h : ((n : ℕ) : WithTop ℚ) ≤ v (x ^ 6)) : ((m : ℕ) : WithTop ℚ) ≤ v x := by sorry
