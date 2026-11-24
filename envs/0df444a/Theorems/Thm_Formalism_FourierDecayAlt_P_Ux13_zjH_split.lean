-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_zjH_split
-- name    : Formalism.FourierDecayAlt.P.Ux13.zjH_split
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:24:47.249902+00:00
-- url     : https://prove2.me/theorems/8e88b53e-3592-4cb7-8bcb-0b4e1a28da11
-- title:
--   Ux13: zj H split
-- statement:
--   The Ux13 construction uses the zj H split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean#L77-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean#L77-L87

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux13
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

theorem Formalism.FourierDecayAlt.P.Ux13.zjH_split (hZ : ZjAffine) {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : XiH p s σ)
    (CC : G.Mat s) :
    (Matrix.of.symm (ZjH σ d η CC) : G.Mat (p + s)) = Matrix.of.symm (ZjH σ d η 0) + iotaL p s CC := by sorry
