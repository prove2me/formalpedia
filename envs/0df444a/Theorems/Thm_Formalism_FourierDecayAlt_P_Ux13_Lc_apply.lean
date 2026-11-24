-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_Lc_apply
-- name    : Formalism.FourierDecayAlt.P.Ux13.Lc_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:24:31.76993+00:00
-- url     : https://prove2.me/theorems/9dac7667-ddcb-49cb-9ec3-0fbc45af9230
-- title:
--   Ux13: Lc apply
-- statement:
--   The Ux13 construction uses the Lc apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean#L192-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean#L192-L192

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

theorem Formalism.FourierDecayAlt.P.Ux13.Lc_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : ℂ) (v : V) : Lc c v = c • v := by sorry
