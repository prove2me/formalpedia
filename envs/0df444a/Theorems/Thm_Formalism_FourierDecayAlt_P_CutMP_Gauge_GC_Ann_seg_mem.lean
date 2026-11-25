-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_seg_mem
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.seg_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:00.778831+00:00
-- url     : https://prove2.me/theorems/a32b6677-74c1-4cc9-a54b-7e35fd322e63
-- title:
--   Ann: seg mem
-- statement:
--   The Ann construction uses the seg mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtPrim.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtPrim.lean#L13-L16

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.seg_mem (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) {x : ℂ} (hx : x ∈ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    seg w₀ x t ∈ S := by sorry
