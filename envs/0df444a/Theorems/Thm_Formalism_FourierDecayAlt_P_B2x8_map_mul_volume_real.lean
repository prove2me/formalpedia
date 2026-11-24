-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_map_mul_volume_real
-- name    : Formalism.FourierDecayAlt.P.B2x8.map_mul_volume_real
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:59:58.575077+00:00
-- url     : https://prove2.me/theorems/7a2cab7e-f6f6-4e1d-aa99-d799b17b7d7e
-- title:
--   B2x8: map mul volume real
-- statement:
--   The B2x8 construction uses the map mul volume real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L467-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L467-L469

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

theorem Formalism.FourierDecayAlt.P.B2x8.map_mul_volume_real (t : ℝ) (ht : t ≠ 0) :
    (volume : Measure ℝ).map (fun s => t * s) = ENNReal.ofReal (|t|⁻¹) • volume := by sorry
