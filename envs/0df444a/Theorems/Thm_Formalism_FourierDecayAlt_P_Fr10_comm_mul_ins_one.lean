-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_comm_mul_ins_one
-- name    : Formalism.FourierDecayAlt.P.Fr10.comm_mul_ins_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:11.687062+00:00
-- url     : https://prove2.me/theorems/f14d6cf3-aa32-4294-88b1-67a8d13e66a2
-- title:
--   Fr10: comm mul ins one
-- statement:
--   The Fr10 construction uses the comm mul ins one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L109-L111

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

theorem Formalism.FourierDecayAlt.P.Fr10.comm_mul_ins_one {a : S} {u w : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (fw : FreeOf a w) (huw : Commute u w)
    (hwM : ∀ i j, Commute w (M i j)) : Commute (u * ins a M) w := by sorry
