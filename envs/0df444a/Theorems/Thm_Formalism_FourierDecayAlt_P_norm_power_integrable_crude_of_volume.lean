-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_norm_power_integrable_crude_of_volume
-- name    : Formalism.FourierDecayAlt.P.norm_power_integrable_crude_of_volume
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:50.053853+00:00
-- url     : https://prove2.me/theorems/d993b576-ad84-483c-b133-4f7b9bfb1178
-- title:
--   P: norm power integrable crude of volume
-- statement:
--   The P construction uses the norm power integrable crude of volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormBallVolumes.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormBallVolumes.lean#L118-L122

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.NormBallVolumes

theorem Formalism.FourierDecayAlt.P.norm_power_integrable_crude_of_volume : Formalism.FourierDecayAlt.B2.GNIntCrudeFromVol := by sorry
