-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs1_jConv_of_jDom
-- name    : Formalism.FourierDecayAlt.P.JFxDs1.jConv_of_jDom
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:24.308634+00:00
-- url     : https://prove2.me/theorems/f1763e7d-0c0c-42c8-b996-e83d281c25cb
-- title:
--   JFx Ds1: j Conv of j Dom
-- statement:
--   The JFx Ds1 construction uses the j Conv of j Dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JConvOfJDom.lean#L14-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JConvOfJDom.lean#L14-L45

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JConvOfJDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.JFxDs1.jConv_of_jDom : Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.JF.JConv := by sorry
