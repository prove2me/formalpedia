-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cmHalfIntegralGenerator_mem_algebraicClosure
-- name    : Formalism.FourierDecayAlt.P.B2x8.cmHalfIntegralGenerator_mem_algebraicClosure
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:43:11.499228+00:00
-- url     : https://prove2.me/theorems/5a4387b5-681a-4acf-816a-e2bc2554cd70
-- title:
--   B2x8: cm Half Integral Generator mem algebraic Closure
-- statement:
--   The B2x8 construction uses the cm Half Integral Generator mem algebraic Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L903-L911
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L903-L911

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x8.cmHalfIntegralGenerator_mem_algebraicClosure (c : ℂ) (hc : c ≠ 0) : w0 k r' c ∈ GV k (1 + r') := by sorry
