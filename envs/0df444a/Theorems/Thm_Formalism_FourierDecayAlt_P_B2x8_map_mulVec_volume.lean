-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_map_mulVec_volume
-- name    : Formalism.FourierDecayAlt.P.B2x8.map_mulVec_volume
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:08.875479+00:00
-- url     : https://prove2.me/theorems/2f68c68e-d708-4232-9717-4cbabdb4a1ca
-- title:
--   B2x8: map mul Vec volume
-- statement:
--   The B2x8 construction uses the map mul Vec volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L450-L458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L450-L458

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

theorem Formalism.FourierDecayAlt.P.B2x8.map_mulVec_volume {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) :
    (volume : Measure (Fin n → ℂ)).map (fun y => A *ᵥ y) = ENNReal.ofReal ((‖A.det‖ ^ 2)⁻¹) • volume := by sorry
