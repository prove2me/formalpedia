-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_contDiff_corner
-- name    : Formalism.FourierDecayAlt.P.PBJ.Frz.contDiff_corner
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:06:28.874929+00:00
-- url     : https://prove2.me/theorems/c990a766-79c2-4612-9d60-96965590d34f
-- title:
--   Frz: cont Diff corner
-- statement:
--   The Frz construction uses the cont Diff corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L361-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockTwoDiagonalZeroSize.lean#L361-L370

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBJ Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Formalism.FourierDecayAlt.P.PBJ.Frz.contDiff_corner (p : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : G.Mat p × AB p => cornerA q.2.1 + cornerB q.2.2) := by sorry
