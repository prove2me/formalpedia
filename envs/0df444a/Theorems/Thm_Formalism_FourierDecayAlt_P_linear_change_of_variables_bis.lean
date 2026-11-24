-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_linear_change_of_variables_bis
-- name    : Formalism.FourierDecayAlt.P.linear_change_of_variables_bis
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:39:16.43785+00:00
-- url     : https://prove2.me/theorems/55e91fb4-3116-4339-9865-4f0db8c8644c
-- title:
--   P: linear change of variables bis
-- statement:
--   The P construction uses the linear change of variables bis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LinearChangeOfVariablesBis.lean#L84-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LinearChangeOfVariablesBis.lean#L84-L98

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x6 C2x7

theorem Formalism.FourierDecayAlt.P.linear_change_of_variables_bis : C2.LinCOV := by sorry
