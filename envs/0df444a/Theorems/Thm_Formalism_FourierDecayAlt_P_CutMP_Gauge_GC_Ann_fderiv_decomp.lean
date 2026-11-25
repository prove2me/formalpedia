-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_fderiv_decomp
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.fderiv_decomp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:51.9838+00:00
-- url     : https://prove2.me/theorems/4f12a237-251f-5654-ad96-a644f3d5909b
-- title:
--   Ann: fderiv decomp
-- statement:
--   The Ann construction uses the fderiv decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FderivDecomp.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FderivDecomp.lean#L24-L27

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.fderiv_decomp (f : ℂ → ℂ) (ζ v : ℂ) :
    fderiv ℝ f ζ v = wZ f ζ * v + wZb f ζ * (starRingEnd ℂ v) := by sorry
