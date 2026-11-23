-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_liftE_mw
-- name    : Formalism.MainNotions.PlaneGram.TwistData.liftE_mw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:23.416251+00:00
-- url     : https://prove2.me/theorems/041e7d8d-1899-40e1-adc2-b63818bbe0da
-- title:
--   Twist Data: lift E mw
-- statement:
--   The Twist Data construction uses the lift E mw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L338-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L338-L340

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable (D : TwistData K) (p : ℕ)

theorem Formalism.MainNotions.PlaneGram.TwistData.liftE_mw (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    D.liftE p α (D.mw t, a) = α (Sum.inr t, a) / D.P p t := by sorry
