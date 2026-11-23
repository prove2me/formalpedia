-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_monomial
-- name    : Formalism.MainNotions.PlaneGram.ddiv_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:57.244856+00:00
-- url     : https://prove2.me/theorems/f24f9055-a77a-4e11-9480-98dfa820f01e
-- title:
--   Plane Gram: ddiv monomial
-- statement:
--   The Plane Gram construction uses the ddiv monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L42-L48

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
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

theorem Formalism.MainNotions.PlaneGram.ddiv_monomial {σ : Type} (M α : σ →₀ ℕ) (c : K) :
    ddiv M (monomial α c) =
      if M ≤ α then monomial (α - M) (c * α.prod fun x k => (k.choose (M x) : K)) else 0 := by sorry
