-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_th_shift
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.th_shift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:53.343059+00:00
-- url     : https://prove2.me/theorems/8bce629b-e36a-4271-a249-6fae033616d9
-- title:
--   Ann: th shift
-- statement:
--   The Ann construction uses the th shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThShiftInt.lean#L18-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThShiftInt.lean#L18-L40

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ImCircleIntegral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.th_shift (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    th TT α (w + 2 * Real.pi * I) = th TT α w + 2 * (circleIntegral α 0 (TT + 1)).im := by sorry
