-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_Hh_add_period
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.Hh_add_period
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:12.829325+00:00
-- url     : https://prove2.me/theorems/af2b0e73-7e91-4b40-a92c-9f01288d68ae
-- title:
--   Ann: Hh add period
-- statement:
--   The Ann construction uses the Hh add period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FderivDecomp.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FderivDecomp.lean#L59-L61

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.Hh_add_period (TT : ℝ) (w : ℂ) (k : ℤ) : w + (k : ℂ) * (2 * Real.pi * I) ∈ Hh TT ↔ w ∈ Hh TT := by sorry
