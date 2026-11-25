-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_circleIntegral_eq
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.circleIntegral_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:41.229843+00:00
-- url     : https://prove2.me/theorems/b4b6b319-23d5-4f47-b53d-0ab581995c42
-- title:
--   Ann: circle Integral eq
-- statement:
--   The Ann construction uses the circle Integral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaAtBasePointZero.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaAtBasePointZero.lean#L26-L31

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaAtBasePointZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.circleIntegral_eq (hTT : 0 ≤ TT) :
    circleIntegral α 0 (TT + 1) = ∫ θ in (0 : ℝ)..2 * Real.pi, I * bet α (x0 TT + (θ : ℂ) * I) := by sorry
