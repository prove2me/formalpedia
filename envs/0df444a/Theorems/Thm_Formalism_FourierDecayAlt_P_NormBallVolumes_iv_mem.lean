-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_iv_mem
-- name    : Formalism.FourierDecayAlt.P.NormBallVolumes.iv_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:27:50.142726+00:00
-- url     : https://prove2.me/theorems/8d5cfe7f-8536-47d4-9a43-393a6201c5ed
-- title:
--   Norm Ball Volumes: iv mem
-- statement:
--   The Norm Ball Volumes construction uses the iv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormBallVolumes.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormBallVolumes.lean#L41-L43

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NormBallVolumes
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.NormBallVolumes.iv_mem {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : iv g ∈ GV k r := by sorry
