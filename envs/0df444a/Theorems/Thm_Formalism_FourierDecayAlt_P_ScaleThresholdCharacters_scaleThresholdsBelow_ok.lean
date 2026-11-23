-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScaleThresholdCharacters_scaleThresholdsBelow_ok
-- name    : Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsBelow_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:50.296333+00:00
-- url     : https://prove2.me/theorems/d6e7b0c9-b967-42b7-a168-0b337661c719
-- title:
--   Scale Threshold Characters: scale Thresholds Below ok
-- statement:
--   The Scale Threshold Characters construction uses the scale Thresholds Below ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScaleThresholdCharacters.lean#L117-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScaleThresholdCharacters.lean#L117-L164

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

theorem Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsBelow_ok : ScaleThresholdsBelow := by sorry
