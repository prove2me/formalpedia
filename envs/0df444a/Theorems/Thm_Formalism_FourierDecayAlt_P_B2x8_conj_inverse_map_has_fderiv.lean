-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_conj_inverse_map_has_fderiv
-- name    : Formalism.FourierDecayAlt.P.B2x8.conj_inverse_map_has_fderiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:58:02.870513+00:00
-- url     : https://prove2.me/theorems/dc9ffa93-b5e0-4c37-ace5-4315c6b7503c
-- title:
--   B2x8: conj inverse map has fderiv
-- statement:
--   The B2x8 construction uses the conj inverse map has fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L481-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L481-L491

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

theorem Formalism.FourierDecayAlt.P.B2x8.conj_inverse_map_has_fderiv (l c : ℂ) (hc : c ≠ 0) : HasFDerivAt (fun c : ℂ => l / conj c) (mi2D l c) c := by sorry
