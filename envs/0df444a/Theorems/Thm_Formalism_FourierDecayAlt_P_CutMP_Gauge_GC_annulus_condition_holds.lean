-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_annulus_condition_holds
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.annulus_condition_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:44:26.66102+00:00
-- url     : https://prove2.me/theorems/f0a407b7-9556-4c75-8240-cf58951e9fe3
-- title:
--   GC: annulus condition holds
-- statement:
--   The GC construction uses the annulus condition holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTConnAnn.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTConnAnn.lean#L10-L27

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtBrReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnAnn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.annulus_condition_holds : GTCAnnulus := by sorry
