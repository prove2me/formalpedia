-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fk_castAdd
-- name    : Formalism.MainNotions.PlaneGram.TwistData.fk_castAdd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:05:08.255889+00:00
-- url     : https://prove2.me/theorems/f9b22246-4856-4194-9029-b2ef327c4786
-- title:
--   Twist Data: fk cast Add
-- statement:
--   The Twist Data construction uses the fk cast Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L31-L33

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
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
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

theorem Formalism.MainNotions.PlaneGram.TwistData.fk_castAdd (o : Finset (Fin (D.nB j + D.r))) (a : Fin (D.nB j)) :
    D.fk j o (Fin.castAdd D.r a) = D.mb (D.eB j a) := by sorry
