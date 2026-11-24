-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_ae_heisenberg_parameter_ne_zero
-- name    : Formalism.FourierDecayAlt.P.B2x8.ae_heisenberg_parameter_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:18.373588+00:00
-- url     : https://prove2.me/theorems/f2567115-3d01-4cf5-8557-fc157fbb875f
-- title:
--   B2x8: ae heisenberg parameter ne zero
-- statement:
--   The B2x8 construction uses the ae heisenberg parameter ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1275-L1280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1275-L1280

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

theorem Formalism.FourierDecayAlt.P.B2x8.ae_heisenberg_parameter_ne_zero : ∀ᵐ p : ℂ × HPar k r' ∂(μx.prod (volume : Measure (HPar k r'))), p.2.2 ≠ 0 := by sorry
