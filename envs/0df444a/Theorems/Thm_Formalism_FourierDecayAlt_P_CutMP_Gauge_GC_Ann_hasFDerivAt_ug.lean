-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasFDerivAt_ug
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_ug
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:15:39.308388+00:00
-- url     : https://prove2.me/theorems/0cadae65-93d5-44a2-8fd0-d6dae50d75d0
-- title:
--   Ann: has FDeriv At ug
-- statement:
--   The Ann construction uses the has FDeriv At ug property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtBrReal.lean#L22-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtBrReal.lean#L22-L41

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtBrReal
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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_ug (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s)
    (hζ : ζ ∈ An TT) :
    HasFDerivAt (ug TT α s)
      (((ContinuousLinearMap.mul ℝ ℂ) (ug TT α s ζ)).comp
        (I • Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹)))) ζ := by sorry
