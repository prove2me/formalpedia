-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_off_diagonal_lift_bound_of_places
-- name    : Formalism.FourierDecayAlt.P.off_diagonal_lift_bound_of_places
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:55.508699+00:00
-- url     : https://prove2.me/theorems/000399e5-9249-4bd4-a789-f57eccc7aa90
-- title:
--   P: off diagonal lift bound of places
-- statement:
--   The P construction uses the off diagonal lift bound of places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L423-L548
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L423-L548

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism.FourierDecayAlt.P.JCx1.decay Formalism.FourierDecayAlt.TB

theorem Formalism.FourierDecayAlt.P.off_diagonal_lift_bound_of_places : Formalism.FourierDecayAlt.JC.OffDiagonalLiftBoundOfPlaces := by sorry
