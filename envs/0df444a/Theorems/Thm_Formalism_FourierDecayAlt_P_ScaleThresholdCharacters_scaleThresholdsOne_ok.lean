-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScaleThresholdCharacters_scaleThresholdsOne_ok
-- name    : Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsOne_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:03.811503+00:00
-- url     : https://prove2.me/theorems/82d5bc8b-d8f1-4ea4-9c2b-cc01c1751dd8
-- title:
--   Scale Threshold Characters: scale Thresholds One ok
-- statement:
--   The Scale Threshold Characters construction uses the scale Thresholds One ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScaleThresholdCharacters.lean#L105-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScaleThresholdCharacters.lean#L105-L115

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScaleThresholdCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
open Formalism.FourierDecayAlt.PairingProductCorollary

theorem Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsOne_ok : ScaleThresholdsOne := by sorry
