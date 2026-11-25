-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_normSq_exp
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.normSq_exp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:17:45.937561+00:00
-- url     : https://prove2.me/theorems/41d8cac6-6ff2-5a48-85fa-80d316e478b4
-- title:
--   Ann: norm Sq exp
-- statement:
--   The Ann construction uses the norm Sq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FderivDecomp.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FderivDecomp.lean#L31-L35

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.normSq_exp (w : ℂ) : Complex.normSq (Complex.exp w) = Real.exp w.re ^ 2 := by sorry
