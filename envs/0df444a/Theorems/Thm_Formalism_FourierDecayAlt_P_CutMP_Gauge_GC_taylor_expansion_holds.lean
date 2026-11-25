-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_taylor_expansion_holds
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.taylor_expansion_holds
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:16:21.29092+00:00
-- url     : https://prove2.me/theorems/850de0d7-8f0e-4410-9ebe-20e0366cf811
-- title:
--   GC: taylor expansion holds
-- statement:
--   The GC construction uses the taylor expansion holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTTaylor.lean#L176-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTTaylor.lean#L176-L210

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTTaylor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.taylor_expansion_holds : GTCLRTaylor := by sorry
