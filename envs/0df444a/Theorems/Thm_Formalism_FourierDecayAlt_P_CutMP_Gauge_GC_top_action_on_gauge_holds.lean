-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_top_action_on_gauge_holds
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.top_action_on_gauge_holds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:38:20.327061+00:00
-- url     : https://prove2.me/theorems/bd10dee5-0951-5b68-8065-4422e9767847
-- title:
--   GC: top action on gauge holds
-- statement:
--   The GC construction uses the top action on gauge holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTRTopAct.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTRTopAct.lean#L6-L6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActAlg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.top_action_on_gauge_holds : GTRTopAct := by sorry
