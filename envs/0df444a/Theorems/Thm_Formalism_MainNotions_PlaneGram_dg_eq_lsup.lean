-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_eq_lsup
-- name    : Formalism.MainNotions.PlaneGram.dg_eq_lsup
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:59.899651+00:00
-- url     : https://prove2.me/theorems/940b0121-8a8c-4933-b427-78de0445b82a
-- title:
--   Plane Gram: dg eq lsup
-- statement:
--   The Plane Gram construction uses the dg eq lsup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L25-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L25-L25

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

theorem Formalism.MainNotions.PlaneGram.dg_eq_lsup {σ : Type} (f : (σ →₀ ℕ) → K) : dg f = lsup fun α => monomial α (f α) := by sorry
