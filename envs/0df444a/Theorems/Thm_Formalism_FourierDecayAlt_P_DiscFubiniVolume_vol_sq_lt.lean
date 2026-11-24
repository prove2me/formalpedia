-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_vol_sq_lt
-- name    : Formalism.FourierDecayAlt.P.DiscFubiniVolume.vol_sq_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:14:36.828203+00:00
-- url     : https://prove2.me/theorems/45010caf-c520-4325-becc-a6e6a07a048a
-- title:
--   Disc Fubini Volume: vol sq lt
-- statement:
--   The Disc Fubini Volume construction uses the vol sq lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscMeanValue.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscMeanValue.lean#L40-L47

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscMeanValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Metric
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume

theorem Formalism.FourierDecayAlt.P.DiscFubiniVolume.vol_sq_lt (s : ℝ) : volume {b : ℝ | b ^ 2 < s} = ENNReal.ofReal (2 * Real.sqrt s) := by sorry
