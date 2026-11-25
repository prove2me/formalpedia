-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_isOpen_annT
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.isOpen_annT
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:29:04.580964+00:00
-- url     : https://prove2.me/theorems/a61cb2d7-7216-4e2a-9567-cd663aec77c9
-- title:
--   Ph: is Open ann T
-- statement:
--   The Ph construction uses the is Open ann T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCHolPh.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCHolPh.lean#L11-L11

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.isOpen_annT (TT : ℝ) : IsOpen (AnnT TT) := by sorry
