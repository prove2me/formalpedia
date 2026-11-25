-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_clm_decomp
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.clm_decomp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:17:41.191992+00:00
-- url     : https://prove2.me/theorems/0f846cdf-4df4-581e-975e-55fed7c82cf9
-- title:
--   Ann: clm decomp
-- statement:
--   The Ann construction uses the clm decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FderivDecomp.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FderivDecomp.lean#L13-L22

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.clm_decomp (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v = (1 / 2 : ℂ) * (L 1 - I * L I) * v + (1 / 2 : ℂ) * (L 1 + I * L I) * (starRingEnd ℂ v) := by sorry
