-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_sc_comm_diag
-- name    : Formalism.FourierDecayAlt.P.Fr10.sc_comm_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:03.798174+00:00
-- url     : https://prove2.me/theorems/fb7a10df-f00e-43ed-923b-422a520b25ec
-- title:
--   Fr10: sc comm diag
-- statement:
--   The Fr10 construction uses the sc comm diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L187-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L187-L190

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

theorem Formalism.FourierDecayAlt.P.Fr10.sc_comm_diag (α : ℂ) (p s : SlopeTestRemainingChoices S A) :
    (!![α • 1, 0; 0, 1] * !![p, 0; 0, s] : M2 (SlopeTestRemainingChoices S A)) = !![p, 0; 0, s] * !![α • 1, 0; 0, 1] := by sorry
