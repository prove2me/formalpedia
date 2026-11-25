-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_continuousOn_bet
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.continuousOn_bet
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:02.489525+00:00
-- url     : https://prove2.me/theorems/e62cd834-48ee-5a32-9fa0-d71344b546f4
-- title:
--   Ann: continuous On bet
-- statement:
--   The Ann construction uses the continuous On bet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ImCircleIntegral.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ImCircleIntegral.lean#L11-L13

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaAtBasePointZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ImCircleIntegral
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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.continuousOn_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContinuousOn (bet α) (Hh TT) := by sorry
