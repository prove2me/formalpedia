-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_chainSet_pair
-- name    : Formalism.MainNotions.PlaneGram.TwistData.chainSet_pair
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:04:01.681172+00:00
-- url     : https://prove2.me/theorems/1fee54af-5925-47a7-bd76-c9703b98a4e2
-- title:
--   Twist Data: chain Set pair
-- statement:
--   The Twist Data construction uses the chain Set pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L109-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L109-L126

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

theorem Formalism.MainNotions.PlaneGram.TwistData.chainSet_pair (hch : ∀ j i, D.chain j i ⊆ D.LLj j)
    (hnest : ∀ (j : Fin D.J) (i i' : Fin (D.nch j)), i < i' → D.chain j i ⊂ D.chain j i')
    (x y : Σ j : Fin D.J, Fin (D.nch j)) :
    D.chainSet x.1 x.2 ⊆ D.chainSet y.1 y.2 ∨ D.chainSet y.1 y.2 ⊆ D.chainSet x.1 x.2 ∨
      Disjoint (D.chainSet x.1 x.2) (D.chainSet y.1 y.2) := by sorry
