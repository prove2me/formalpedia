-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_monomial
-- name    : Formalism.MainNotions.PlaneGram.TwistData.digitPart_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:05.757604+00:00
-- url     : https://prove2.me/theorems/98a61d58-20ed-41b8-9397-7b7b15b37369
-- title:
--   Twist Data: digit Part monomial
-- statement:
--   The Twist Data construction uses the digit Part monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L94-L99

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
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)

theorem Formalism.MainNotions.PlaneGram.TwistData.digitPart_monomial (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (α : D.EA) (c : K) :
    D.digitPart p ρ (monomial α c) = if D.InClass p ρ α then monomial (D.liftE p α) c else 0 := by sorry
