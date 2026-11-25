-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_circleMap_mem_annT
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.circleMap_mem_annT
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:16:17.803366+00:00
-- url     : https://prove2.me/theorems/8dc82daa-8d89-53c6-90a3-fd2044882b8c
-- title:
--   Ph: circle Map mem ann T
-- statement:
--   The Ph construction uses the circle Map mem ann T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCHolPh.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCHolPh.lean#L13-L16

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.circleMap_mem_annT {TT R : ℝ} (hR : TT < R ^ 2) (θ : ℝ) : circleMap 0 R θ ∈ AnnT TT := by sorry
