-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_dilation_mem_group
-- name    : Formalism.FourierDecayAlt.P.dilation_mem_group
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:29:16.252151+00:00
-- url     : https://prove2.me/theorems/76a82c6b-d82e-49c5-a619-642e1c14b048
-- title:
--   P: dilation mem group
-- statement:
--   The P construction uses the dilation mem group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointnessPolynomiallyBounded.lean#L122-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointnessPolynomiallyBounded.lean#L122-L140

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem Formalism.FourierDecayAlt.P.dilation_mem_group : Formalism.FourierDecayAlt.B.DilMem := by sorry
