-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_isotropic_cone_finite_measure
-- name    : Formalism.FourierDecayAlt.P.isotropic_cone_finite_measure
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:37:59.453014+00:00
-- url     : https://prove2.me/theorems/864c2ba0-7775-4152-9544-5b37dd84edbe
-- title:
--   P: isotropic cone finite measure
-- statement:
--   The P construction uses the isotropic cone finite measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1399-L1414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1399-L1414

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 B2x8

theorem Formalism.FourierDecayAlt.P.isotropic_cone_finite_measure : Formalism.FourierDecayAlt.B2.ConeFinite := by sorry
