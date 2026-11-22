-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_phE_apply_inl
-- name    : Formalism.MainNotions.PlaneGram.TwistData.phE_apply_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:45.757153+00:00
-- url     : https://prove2.me/theorems/a5b8a5f0-ddbb-44cd-8048-6664ff887e3e
-- title:
--   Twist Data: ph E apply inl
-- statement:
--   The Twist Data construction uses the ph E apply inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/Monomial.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/Monomial.lean#L26-L28

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

theorem Formalism.MainNotions.PlaneGram.TwistData.phE_apply_inl (p : ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.phE p ζ (Sum.inl b, a) = ζ (D.mb b, a) := by sorry
