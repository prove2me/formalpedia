-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mem_chainSet
-- name    : Formalism.MainNotions.PlaneGram.TwistData.mem_chainSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:39.342981+00:00
-- url     : https://prove2.me/theorems/beac7207-9cdf-4dea-a797-514bc21a491d
-- title:
--   Twist Data: mem chain Set
-- statement:
--   The Twist Data construction uses the mem chain Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L69-L71

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

theorem Formalism.MainNotions.PlaneGram.TwistData.mem_chainSet (j : Fin D.J) (i : Fin (D.nch j)) (z : D.ML) :
    z ∈ D.chainSet j i ↔ (∃ b ∈ D.chain j i, D.mb b = z) ∨ ∃ m : Fin D.r, D.mw (D.aux₃ j, m) = z := by sorry
