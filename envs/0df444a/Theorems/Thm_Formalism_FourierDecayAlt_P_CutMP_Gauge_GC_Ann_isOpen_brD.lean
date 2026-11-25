-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_isOpen_brD
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.isOpen_brD
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:13:07.056639+00:00
-- url     : https://prove2.me/theorems/39c17dda-9602-5471-95de-6108a120d3ec
-- title:
--   Ann: is Open br D
-- statement:
--   The Ann construction uses the is Open br D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NeZeroOfAn.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NeZeroOfAn.lean#L22-L27

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.isOpen_brD (s : Bool) : IsOpen (brD s) := by sorry
