-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_coeff_GM
-- name    : Formalism.MainNotions.PlaneGram.TwistData.coeff_GM
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:27.949605+00:00
-- url     : https://prove2.me/theorems/bd93c1d5-091e-4f75-b385-4b664db5666d
-- title:
--   Twist Data: coeff GM
-- statement:
--   The Twist Data construction uses the coeff GM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L108-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L108-L123

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
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

theorem Formalism.MainNotions.PlaneGram.TwistData.coeff_GM (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) :
    (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ) =
      (D.ga (D.collapseExponent p ζ))⁻¹ * ((D.ga (D.phE p ζ) * F.coeff (D.phE p ζ)) *
        ((∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x) : ℕ) : K)) := by sorry
