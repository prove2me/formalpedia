-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_monomial
-- name    : Formalism.MainNotions.PlaneGram.lsup_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:06.174803+00:00
-- url     : https://prove2.me/theorems/055cfc98-a7e2-420b-89be-5328d9be1b90
-- title:
--   Plane Gram: lsup monomial
-- statement:
--   The Plane Gram construction uses the lsup monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L14-L17

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

theorem Formalism.MainNotions.PlaneGram.lsup_monomial {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) (α : σ →₀ ℕ) (c : K) :
    lsup φ (monomial α c) = c • φ α := by sorry
