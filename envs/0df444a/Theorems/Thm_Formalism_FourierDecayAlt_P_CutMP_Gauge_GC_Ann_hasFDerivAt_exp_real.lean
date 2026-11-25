-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasFDerivAt_exp_real
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_exp_real
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:13:07.744145+00:00
-- url     : https://prove2.me/theorems/059c4a24-98e1-4500-8d1f-8bbb9f542b52
-- title:
--   Ann: has FDeriv At exp real
-- statement:
--   The Ann construction uses the has FDeriv At exp real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BasePointMemHalfPlane.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BasePointMemHalfPlane.lean#L19-L26

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_exp_real (w : ℂ) :
    HasFDerivAt Complex.exp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w)) w := by sorry
