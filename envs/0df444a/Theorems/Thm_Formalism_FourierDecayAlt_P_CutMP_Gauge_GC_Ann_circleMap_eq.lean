-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_circleMap_eq
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.circleMap_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:34.194796+00:00
-- url     : https://prove2.me/theorems/708bbde7-023f-43b2-8d3e-bb943e560acc
-- title:
--   Ann: circle Map eq
-- statement:
--   The Ann construction uses the circle Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaAtBasePointZero.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaAtBasePointZero.lean#L17-L18

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.circleMap_eq (hTT : 0 ≤ TT) (θ : ℝ) : circleMap 0 (TT + 1) θ = Complex.exp (x0 TT + (θ : ℂ) * I) := by sorry
