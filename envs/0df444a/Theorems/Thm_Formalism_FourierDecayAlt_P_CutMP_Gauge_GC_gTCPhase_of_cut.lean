-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_gTCPhase_of_cut
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTCPhase_of_cut
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:55:29.551162+00:00
-- url     : https://prove2.me/theorems/0bbdff5a-b9e2-4351-bc33-fca35209b4a1
-- title:
--   GC: g TCPhase of cut
-- statement:
--   The GC construction uses the g TCPhase of cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/cut_GCore_GTConnCut.lean#L136-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/cut_GCore_GTConnCut.lean#L136-L154

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGenTransferCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTCPhase_of_cut : GTCPhaseOfCut := by sorry
