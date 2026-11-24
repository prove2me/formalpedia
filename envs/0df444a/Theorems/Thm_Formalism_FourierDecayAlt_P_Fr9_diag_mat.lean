-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_diag_mat
-- name    : Formalism.FourierDecayAlt.P.Fr9.diag_mat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:02:58.472051+00:00
-- url     : https://prove2.me/theorems/0c3836d1-9e4c-426d-b595-88d5de7ff0c4
-- title:
--   Fr9: diag mat
-- statement:
--   The Fr9 construction uses the diag mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L297-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L297-L304

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

theorem Formalism.FourierDecayAlt.P.Fr9.diag_mat (τ : SlopeTestRemainingChoices S A) {d : ℂ} (hd : d - 1 ≠ 0) :
    d0 τ * !![(d / (d - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] = (d - 1)⁻¹ • !![d • τ, 0; 0, (d - 1) • τ] := by sorry
