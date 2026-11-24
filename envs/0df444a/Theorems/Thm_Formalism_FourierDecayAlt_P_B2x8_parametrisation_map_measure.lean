-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_parametrisation_map_measure
-- name    : Formalism.FourierDecayAlt.P.B2x8.parametrisation_map_measure
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:59:43.921991+00:00
-- url     : https://prove2.me/theorems/5c2955cc-22a0-40cf-b835-cfd442b9d975
-- title:
--   B2x8: parametrisation map measure
-- statement:
--   The B2x8 construction uses the parametrisation map measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L714-L735
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L714-L735

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

theorem Formalism.FourierDecayAlt.P.B2x8.parametrisation_map_measure :
    (((volume : Measure ℂ).withDensity fun c => ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1)))).prod
      (volume : Measure (HPar k r'))).map (cm1Θ k r') = μx.prod volume := by sorry
