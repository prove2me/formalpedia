-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_dilation_jacobian_of_parts
-- name    : Formalism.FourierDecayAlt.P.dilation_jacobian_of_parts
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:30:05.713424+00:00
-- url     : https://prove2.me/theorems/996dff98-b7a7-450a-983c-2104c99fe965
-- title:
--   P: dilation jacobian of parts
-- statement:
--   The P construction uses the dilation jacobian of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1511-L1537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1511-L1537

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x8

theorem Formalism.FourierDecayAlt.P.dilation_jacobian_of_parts : Formalism.FourierDecayAlt.B2.AssembleDilJac := by sorry
