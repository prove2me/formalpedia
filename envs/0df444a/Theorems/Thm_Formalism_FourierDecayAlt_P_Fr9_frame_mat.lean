-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_frame_mat
-- name    : Formalism.FourierDecayAlt.P.Fr9.frame_mat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:02:30.905794+00:00
-- url     : https://prove2.me/theorems/b2a66fab-c1be-407b-9b8d-b3a9a4023bd7
-- title:
--   Fr9: frame mat
-- statement:
--   The Fr9 construction uses the frame mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L291-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L291-L295

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
variable {b : S}
variable {L : LevelData A r} {f : FrameData S A}

theorem Formalism.FourierDecayAlt.P.Fr9.frame_mat (L : LevelData A r) (m : SlopeTestRemainingChoices S A) :
    (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * m, io L.GG] : M2 (SlopeTestRemainingChoices S A)) =
      !![io L.ζbi, 0; io L.ζi * io L.GG * m, io L.ζi * io L.GG] := by sorry
