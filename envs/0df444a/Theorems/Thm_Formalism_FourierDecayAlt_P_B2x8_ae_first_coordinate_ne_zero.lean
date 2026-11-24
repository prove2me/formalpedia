-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_ae_first_coordinate_ne_zero
-- name    : Formalism.FourierDecayAlt.P.B2x8.ae_first_coordinate_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:59:30.783579+00:00
-- url     : https://prove2.me/theorems/e5943d49-189f-4905-8397-47867729ed49
-- title:
--   B2x8: ae first coordinate ne zero
-- statement:
--   The B2x8 construction uses the ae first coordinate ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1269-L1273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1269-L1273

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

theorem Formalism.FourierDecayAlt.P.B2x8.ae_first_coordinate_ne_zero : ∀ᵐ p : ℂ × HPar k r' ∂(μx.prod (volume : Measure (HPar k r'))), p.1 ≠ 0 := by sorry
