-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_curv_alg
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.curv_alg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:24:04.095903+00:00
-- url     : https://prove2.me/theorems/5a8e912e-2586-442f-af77-0cffdd1819f9
-- title:
--   Ph: curv alg
-- statement:
--   The Ph construction uses the curv alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCHolPh.lean#L170-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCHolPh.lean#L170-L177

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.curv_alg (u0 p q s11 sii : ℂ) (hn : u0 * star u0 = 1) (ha : (star u0 * p).re = 0)
    (hb : (star u0 * q).re = 0) (h11 : (star p * p + star u0 * s11).re = 0)
    (hII : (star q * q + star u0 * sii).re = 0) :
    ((star p + Complex.I * star q) * (p - Complex.I * q) + star u0 * (s11 + sii)).re = 0 := by sorry
