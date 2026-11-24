-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_dilation_map_measure
-- name    : Formalism.FourierDecayAlt.P.B2x8.heisenberg_dilation_map_measure
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:00:29.763076+00:00
-- url     : https://prove2.me/theorems/93a49937-d1d2-4a7d-82da-24cfb314f66e
-- title:
--   B2x8: heisenberg dilation map measure
-- statement:
--   The B2x8 construction uses the heisenberg dilation map measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L698-L708
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L698-L708

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

theorem Formalism.FourierDecayAlt.P.B2x8.heisenberg_dilation_map_measure (c : ℂ) (hc : c ≠ 0) :
    (volume : Measure (HPar k r')).map (fun x : HPar k r' => (c • x.1, ‖c‖ ^ 2 * x.2)) =
      ENNReal.ofReal ((‖c‖ ^ (2 * (2 * r' + k + 1) + 2))⁻¹) • volume := by sorry
