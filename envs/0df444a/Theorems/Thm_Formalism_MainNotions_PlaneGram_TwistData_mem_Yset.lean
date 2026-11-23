-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mem_Yset
-- name    : Formalism.MainNotions.PlaneGram.TwistData.mem_Yset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:35.639936+00:00
-- url     : https://prove2.me/theorems/db3f286f-ffc5-47d9-bb30-ed7a9a21b082
-- title:
--   Twist Data: mem Yset
-- statement:
--   The Twist Data construction uses the mem Yset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L73-L76

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
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

theorem Formalism.MainNotions.PlaneGram.TwistData.mem_Yset (j : Fin D.J) (m : Fin D.r) (z : D.ML) :
    z ∈ D.Yset j m ↔ (∃ m' : Fin D.r, D.mw (D.aux₃ j, m') = z) ∨ (∃ b ∈ D.LLj j, D.mb b = z) ∨
      ∃ m' : Fin D.r, m < m' ∧ D.mtp (j, m') = z := by sorry
