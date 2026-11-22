-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_eq
-- name    : Formalism.MainNotions.PlaneGram.TwistData.digitPart_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:23.159163+00:00
-- url     : https://prove2.me/theorems/10fcea0c-608a-425d-8eaa-ceebd1275baf
-- title:
--   Twist Data: digit Part eq
-- statement:
--   The Twist Data construction uses the digit Part eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L86-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L86-L92

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
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

theorem Formalism.MainNotions.PlaneGram.TwistData.digitPart_eq (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ F = D.digitPartL p ρ F := by sorry
