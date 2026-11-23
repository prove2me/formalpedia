-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_putL_monomial
-- name    : Formalism.MainNotions.PlaneGram.putL_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:43.868797+00:00
-- url     : https://prove2.me/theorems/01755547-6bb0-48d6-b496-74e65b55c0b5
-- title:
--   Plane Gram: put L monomial
-- statement:
--   The Plane Gram construction uses the put L monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L238-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L238-L240

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}

theorem Formalism.MainNotions.PlaneGram.putL_monomial (i : L) (α : L × Fin r →₀ ℕ) (η : Fin r →₀ ℕ) (c : K) :
    putL i α (monomial η c) = monomial (offE i α + onLetter i η) c := by sorry
