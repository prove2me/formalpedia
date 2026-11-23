-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_inv_mul_ins
-- name    : Formalism.FourierDecayAlt.P.Fr10.inv_mul_ins
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:25.466806+00:00
-- url     : https://prove2.me/theorems/beeca3ad-ad05-4951-9fd7-38745d054ced
-- title:
--   Fr10: inv mul ins
-- statement:
--   The Fr10 construction uses the inv mul ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L113-L119

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Fr10.inv_mul_ins {a : S} {u ui : SlopeTestRemainingChoices S A} {M Mi : M2 (SlopeTestRemainingChoices S A)} (fui : FreeOf a ui) (fM : FreeOf2 a M)
    (h : u * ui = 1) (hc : ∀ i j, Commute ui (M i j)) (hM : M * Mi = 1) :
    u * ins a M * (ui * ins a Mi) = 1 := by sorry
