-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_lintegral_inv_norm_lt_top
-- name    : Formalism.FourierDecayAlt.P.B2x8.lintegral_inv_norm_lt_top
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:00:07.694447+00:00
-- url     : https://prove2.me/theorems/c558bfa3-fbc5-46da-b822-a1246ee3b88e
-- title:
--   B2x8: lintegral inv norm lt top
-- statement:
--   The B2x8 construction uses the lintegral inv norm lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L563-L590
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L563-L590

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

theorem Formalism.FourierDecayAlt.P.B2x8.lintegral_inv_norm_lt_top (R : ℝ) :
    (∫⁻ c in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (‖c‖⁻¹)) < ∞ := by sorry
