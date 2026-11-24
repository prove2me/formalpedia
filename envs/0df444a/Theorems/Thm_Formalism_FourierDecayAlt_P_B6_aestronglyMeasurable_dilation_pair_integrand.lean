-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aestronglyMeasurable_dilation_pair_integrand
-- name    : Formalism.FourierDecayAlt.P.B6.aestronglyMeasurable_dilation_pair_integrand
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:01:30.686373+00:00
-- url     : https://prove2.me/theorems/3c99b388-0d49-4068-806c-9db859fedb28
-- title:
--   B6: aestrongly Measurable dilation pair integrand
-- statement:
--   The B6 construction uses the aestrongly Measurable dilation pair integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2998-L3008
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2998-L3008

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem Formalism.FourierDecayAlt.P.B6.aestronglyMeasurable_dilation_pair_integrand (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : admitted α c F)
    (hF' : admitted α c' F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    AEStronglyMeasurable (fourierWeightedPhase D F F' w₁ w₂) D.μSS := by sorry
