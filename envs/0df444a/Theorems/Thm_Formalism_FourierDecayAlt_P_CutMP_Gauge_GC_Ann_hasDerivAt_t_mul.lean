-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasDerivAt_t_mul
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasDerivAt_t_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:53.613934+00:00
-- url     : https://prove2.me/theorems/16d0b25c-f55c-51a8-8e41-02edaa93b533
-- title:
--   Ann: has Deriv At t mul
-- statement:
--   The Ann construction uses the has Deriv At t mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtTMul.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtTMul.lean#L13-L29

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtTMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasDerivAt_t_mul (hω : ∀ p ∈ S, HasFDerivAt ω (fderiv ℝ ω p) p)
    (hsym : ∀ p ∈ S, ∀ h k : ℂ, fderiv ℝ ω p h k = fderiv ℝ ω p k h) {w : ℂ} {t : ℝ}
    (hγ : w₀ + (t : ℂ) * (w - w₀) ∈ S) (h : ℂ) :
    HasDerivAt (fun s : ℝ => s * ω (w₀ + (s : ℂ) * (w - w₀)) h)
      (ω (w₀ + (t : ℂ) * (w - w₀)) h + t * fderiv ℝ ω (w₀ + (t : ℂ) * (w - w₀)) h (w - w₀)) t := by sorry
