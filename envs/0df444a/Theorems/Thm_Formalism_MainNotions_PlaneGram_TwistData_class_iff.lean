-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_class_iff
-- name    : Formalism.MainNotions.PlaneGram.TwistData.class_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:04:13.718455+00:00
-- url     : https://prove2.me/theorems/6222a2c3-bca9-45bc-9d58-4435252c8da6
-- title:
--   Twist Data: class iff
-- statement:
--   The Twist Data construction uses the class iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L29-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L29-L76

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

theorem Formalism.MainNotions.PlaneGram.TwistData.class_iff (p : ℕ) {ζ : D.EM} (hζ : D.LabLowE p ζ) (α : D.EA) :
    (D.InClass p (D.labF ζ) α ∧ D.liftE p α = eIn D.outP ζ) ↔ α = D.collapseExponent p ζ := by sorry
