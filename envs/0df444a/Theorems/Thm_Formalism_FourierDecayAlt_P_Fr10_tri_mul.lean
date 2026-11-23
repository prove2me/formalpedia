-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_tri_mul
-- name    : Formalism.FourierDecayAlt.P.Fr10.tri_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:17.157178+00:00
-- url     : https://prove2.me/theorems/98813e17-25c6-4ecc-aed9-9d865f249b82
-- title:
--   Fr10: tri mul
-- statement:
--   The Fr10 construction uses the tri mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L158-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L158-L166

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
variable {r : ℕ} (L : LevelData A r) (f : FrameData S A)

theorem Formalism.FourierDecayAlt.P.Fr10.tri_mul (m : SlopeTestRemainingChoices S A) :
    (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * m, io L.GG]) *
      (!![1, 0; -m, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ]) = (1 : M2 (SlopeTestRemainingChoices S A)) := by sorry
