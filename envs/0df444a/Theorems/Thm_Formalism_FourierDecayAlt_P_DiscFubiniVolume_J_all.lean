-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_J_all
-- name    : Formalism.FourierDecayAlt.P.DiscFubiniVolume.J_all
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:12:38.097542+00:00
-- url     : https://prove2.me/theorems/057ac28a-4274-4068-abc3-8d4876426889
-- title:
--   Disc Fubini Volume: J all
-- statement:
--   The Disc Fubini Volume construction uses the J all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscMeanValue.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscMeanValue.lean#L11-L38

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

theorem Formalism.FourierDecayAlt.P.DiscFubiniVolume.J_all {u : ℝ} (hu : 0 < u) :
    ‖∫ t in (-1 : ℝ)..1, (g0 t : ℂ) * ee u t‖ ≤ 10 / (u * Real.sqrt u) := by sorry
