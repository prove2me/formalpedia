-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_En_trace_smoothness
-- name    : Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:30:00.939946+00:00
-- url     : https://prove2.me/theorems/21f380bf-1433-5d2b-9e7b-02ac2b9db78f
-- title:
--   En: trace smoothness
-- statement:
--   The En construction uses the trace smoothness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnTrSmooth.lean#L45-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnTrSmooth.lean#L45-L91

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnFibMem
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOpenDomain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnTrSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness : TrSmooth := by sorry
