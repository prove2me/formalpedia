-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_gTSSLocal_of_cut
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTSSLocal_of_cut
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:30:10.471405+00:00
-- url     : https://prove2.me/theorems/4ac3a9aa-4196-539a-a87f-0d0c9249201e
-- title:
--   GC: g TSSLocal of cut
-- statement:
--   The GC construction uses the g TSSLocal of cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTSSLocalCut.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTSSLocalCut.lean#L48-L53

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLocalCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSLocalCut
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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTSSLocal_of_cut : GTSSLocalOfCut := by sorry
