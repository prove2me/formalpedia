-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_continuousOn_g2_symmetric_interval
-- name    : Formalism.FourierDecayAlt.P.DiscFubiniVolume.continuousOn_g2_symmetric_interval
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:54.096996+00:00
-- url     : https://prove2.me/theorems/f811a919-cb73-4b7f-a740-88adfee7df8b
-- title:
--   Disc Fubini Volume: continuous On g2 symmetric interval
-- statement:
--   The Disc Fubini Volume construction uses the continuous On g2 symmetric interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean#L104-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean#L104-L112

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory intervalIntegral Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume

theorem Formalism.FourierDecayAlt.P.DiscFubiniVolume.continuousOn_g2_symmetric_interval {a : ℝ} (ha : a < 1) (ha0 : 0 ≤ a) : ContinuousOn g2 (uIcc (-a) a) := by sorry
