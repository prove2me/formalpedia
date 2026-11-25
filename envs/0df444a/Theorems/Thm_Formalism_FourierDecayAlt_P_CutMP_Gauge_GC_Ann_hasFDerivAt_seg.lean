-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasFDerivAt_seg
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_seg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:18:11.421567+00:00
-- url     : https://prove2.me/theorems/5377010b-17c2-436d-9a89-3bcef2083a5e
-- title:
--   Ann: has FDeriv At seg
-- statement:
--   The Ann construction uses the has FDeriv At seg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtPrim.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtPrim.lean#L29-L37

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtTMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory intervalIntegral Metric
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_seg (x : ℂ) (t : ℝ) :
    HasFDerivAt (fun y : ℂ => seg w₀ y t) ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ) x := by sorry
