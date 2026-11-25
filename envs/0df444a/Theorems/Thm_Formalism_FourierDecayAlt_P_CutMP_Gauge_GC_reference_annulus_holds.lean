-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_reference_annulus_holds
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.reference_annulus_holds
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:29:36.631153+00:00
-- url     : https://prove2.me/theorems/aa49cf35-4e68-4284-8676-3dd801a57eab
-- title:
--   GC: reference annulus holds
-- statement:
--   The GC construction uses the reference annulus holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCRefAn.lean#L9-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCRefAn.lean#L9-L35

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCRefCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCRefAn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.reference_annulus_holds : GTCRefAn := by sorry
