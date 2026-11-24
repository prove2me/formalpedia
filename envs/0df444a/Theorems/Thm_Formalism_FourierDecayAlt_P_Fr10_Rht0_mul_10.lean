-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_Rht0_mul_10
-- name    : Formalism.FourierDecayAlt.P.Fr10.Rht0_mul_10
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:01.448699+00:00
-- url     : https://prove2.me/theorems/f57a28c0-2b87-4ea6-bfa7-2a8451457dc7
-- title:
--   Fr10: Rht0 mul 10
-- statement:
--   The Fr10 construction uses the Rht0 mul 10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L135-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L135-L145

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

theorem Formalism.FourierDecayAlt.P.Fr10.Rht0_mul_10 (b : S) (d : ℂ) (M : M2 (SlopeTestRemainingChoices S A)) :
    (Rht0 b d * M : M2 (SlopeTestRemainingChoices S A)) 1 0 = (d - 1)⁻¹ • ins b !![d • M 1 0, 0; -M 0 0, (d - 1) • M 1 0] := by sorry
