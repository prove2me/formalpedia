-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_integral_dilation_pair_integrand_eq
-- name    : Formalism.FourierDecayAlt.P.B6.integral_dilation_pair_integrand_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:02:54.759076+00:00
-- url     : https://prove2.me/theorems/1e58b04d-5f00-4329-8e9b-e77e65d8469d
-- title:
--   B6: integral dilation pair integrand eq
-- statement:
--   The B6 construction uses the integral dilation pair integrand eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L3042-L3052
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L3042-L3052

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

theorem Formalism.FourierDecayAlt.P.B6.integral_dilation_pair_integrand_eq (H : Hyp D Ξ α) (hJ : DilJac D) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : admitted α c F) (hF' : admitted α c' F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) {t : ℝ × ℝ}
    (h1 : 0 < t.1) (h2 : 0 < t.2) :
    (∫ p, fourierWeightedPhase D F F' w₁ w₂ (dilation₂ t p) ∂D.μSS) =
      ((((t.1 * t.2) ^ kap k r)⁻¹ : ℝ) : ℂ) * ∫ p, fourierWeightedPhase D F F' w₁ w₂ p ∂D.μSS := by sorry
