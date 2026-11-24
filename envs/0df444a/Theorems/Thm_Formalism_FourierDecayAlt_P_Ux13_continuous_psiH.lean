-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_psiH
-- name    : Formalism.FourierDecayAlt.P.Ux13.continuous_psiH
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:23:08.91918+00:00
-- url     : https://prove2.me/theorems/c87b9371-6814-45f5-8d19-8301dd074747
-- title:
--   Ux13: continuous psi H
-- statement:
--   The Ux13 construction uses the continuous psi H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean#L147-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean#L147-L160

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

theorem Formalism.FourierDecayAlt.P.Ux13.continuous_psiH {p s : ℕ} (β : ℂ) (σ : Equiv.Perm (Fin p)) :
    Continuous fun η : XiH p s σ => psiH β σ η := by sorry
