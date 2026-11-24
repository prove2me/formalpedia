-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_parametric_derivative_under_integral
-- name    : Formalism.FourierDecayAlt.P.B6.parametric_derivative_under_integral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:04:05.826457+00:00
-- url     : https://prove2.me/theorems/8206ec2d-6c09-4285-b6f1-f8319d0da256
-- title:
--   B6: parametric derivative under integral
-- statement:
--   The B6 construction uses the parametric derivative under integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1157-L1195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1157-L1195

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

theorem Formalism.FourierDecayAlt.P.B6.parametric_derivative_under_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (hL : ∀ T, ‖L T‖ ≤ ‖T‖)
    {u v u' v' : ℝ → X → (Wq →L[ℂ] Wp)} {y₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 y₀) {m : X → ℝ} {C : ℝ}
    (hm : Integrable (fun g => m g * m g) μ)
    (mu : ∀ y ∈ s, AEStronglyMeasurable (u y) μ) (mv : ∀ y ∈ s, AEStronglyMeasurable (v y) μ)
    (mu' : ∀ y ∈ s, AEStronglyMeasurable (u' y) μ) (mv' : ∀ y ∈ s, AEStronglyMeasurable (v' y) μ)
    (du : ∀ᵐ g ∂μ, ∀ y ∈ s, HasDerivAt (fun y => u y g) (u' y g) y)
    (dv : ∀ᵐ g ∂μ, ∀ y ∈ s, HasDerivAt (fun y => v y g) (v' y g) y)
    (bu : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖u y g‖ ≤ C * m g) (bv : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖v y g‖ ≤ C * m g)
    (bu' : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖u' y g‖ ≤ C * m g) (bv' : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖v' y g‖ ≤ C * m g) :
    HasDerivAt (fun y => ∫ g, hsInner (L (u y g)) (v y g) ∂μ)
      (∫ g, (hsInner (L (u' y₀ g)) (v y₀ g) + hsInner (L (u y₀ g)) (v' y₀ g)) ∂μ) y₀ := by sorry
