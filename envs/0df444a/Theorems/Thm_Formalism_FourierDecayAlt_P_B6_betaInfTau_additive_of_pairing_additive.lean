-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_betaInfTau_additive_of_pairing_additive
-- name    : Formalism.FourierDecayAlt.P.B6.betaInfTau_additive_of_pairing_additive
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:01:04.292443+00:00
-- url     : https://prove2.me/theorems/6f27e224-88af-49f1-941b-45fd21dea48c
-- title:
--   B6: beta Inf Tau additive of pairing additive
-- statement:
--   The B6 construction uses the beta Inf Tau additive of pairing additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2680-L2698
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2680-L2698

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

theorem Formalism.FourierDecayAlt.P.B6.betaInfTau_additive_of_pairing_additive (H : Hyp D Ξ α) {X Y X₁ Y₁ X₂ Y₂ : Mat k r → (Wq →L[ℂ] Wp)} {c₁ c₁' c₂ c₂' : ℝ}
    (hX₁ : AdmW α c₁ 2 2 X₁) (hY₁ : AdmW α c₁' 2 2 Y₁) (hX₂ : AdmW α c₂ 2 2 X₂) (hY₂ : AdmW α c₂' 2 2 Y₂)
    (h : ∀ q, D.inSS q → Ph D X Y q = Ph D X₁ Y₁ q + Ph D X₂ Y₂ q) {τ : ℝ × ℝ} (hτ : τ ∈ Quad) :
    betaInfTau D τ X Y = betaInfTau D τ X₁ Y₁ + betaInfTau D τ X₂ Y₂ := by sorry
