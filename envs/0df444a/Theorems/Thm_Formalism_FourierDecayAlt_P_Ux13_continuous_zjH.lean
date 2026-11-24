-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_zjH
-- name    : Formalism.FourierDecayAlt.P.Ux13.continuous_zjH
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:22:54.098421+00:00
-- url     : https://prove2.me/theorems/106984c9-3af9-4a34-99d7-3907fccfa6c9
-- title:
--   Ux13: continuous zj H
-- statement:
--   The Ux13 construction uses the continuous zj H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean#L162-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean#L162-L177

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

theorem Formalism.FourierDecayAlt.P.Ux13.continuous_zjH {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (CC : G.Mat s) :
    Continuous fun η : XiH p s σ => (Matrix.of.symm (ZjH σ d η CC) : G.Mat (p + s)) := by sorry
