-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_gaAct_eq
-- name    : Formalism.MainNotions.PlaneGram.TwistData.gaAct_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:05:14.179937+00:00
-- url     : https://prove2.me/theorems/922e0f6d-f85e-4b75-8420-bf75d95d83f8
-- title:
--   Twist Data: ga Act eq
-- statement:
--   The Twist Data construction uses the ga Act eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L114-L115

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

theorem Formalism.MainNotions.PlaneGram.TwistData.gaAct_eq (G : MvPolynomial (D.OL × Fin D.r) K) : D.gaAct G = dg D.ga G := by sorry
