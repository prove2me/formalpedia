-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_phE_apply_inr
-- name    : Formalism.MainNotions.PlaneGram.TwistData.phE_apply_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:29.469682+00:00
-- url     : https://prove2.me/theorems/6ed359e9-1556-460f-985d-8844fec75fbf
-- title:
--   Twist Data: ph E apply inr
-- statement:
--   The Twist Data construction uses the ph E apply inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/Monomial.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/Monomial.lean#L30-L32

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)

theorem Formalism.MainNotions.PlaneGram.TwistData.phE_apply_inr (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.phE p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) + ζ (D.mtp t, a) := by sorry
