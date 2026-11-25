-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasFDerivAt_br_real
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_br_real
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:13:33.73353+00:00
-- url     : https://prove2.me/theorems/d0905567-a6e6-4f77-a36f-d62dc3255e84
-- title:
--   Ann: has FDeriv At br real
-- statement:
--   The Ann construction uses the has FDeriv At br real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtBrReal.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtBrReal.lean#L13-L20

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_br_real (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) :
    HasFDerivAt (br s) ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹) ζ := by sorry
