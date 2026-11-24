-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_fourier_slice_in_x
-- name    : Formalism.FourierDecayAlt.P.B6.fourier_slice_in_x
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:02:18.674848+00:00
-- url     : https://prove2.me/theorems/a2398fc6-53f3-4fc1-980e-8c2be184f3e4
-- title:
--   B6: fourier slice in x
-- statement:
--   The B6 construction uses the fourier slice in x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1689-L1705
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1689-L1705

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

theorem Formalism.FourierDecayAlt.P.B6.fourier_slice_in_x {K K' : ℝ → ℝ → ℂ} (x₁ x₂ : ℝ) (c : ℂ)
    (hK : Integrable fun t : ℝ × ℝ => K t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)))
    (hK' : Integrable fun t : ℝ × ℝ => K' t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)))
    (h : ∀ y, (∫ x, K x y * Complex.exp (Complex.I * ((x₁ * x : ℝ) : ℂ))) =
      c * ∫ x, K' x y * Complex.exp (Complex.I * ((x₁ * x : ℝ) : ℂ))) :
    (∫ t : ℝ × ℝ, K t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      c * ∫ t : ℝ × ℝ, K' t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by sorry
