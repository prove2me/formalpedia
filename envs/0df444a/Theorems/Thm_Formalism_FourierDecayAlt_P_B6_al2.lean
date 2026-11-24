-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_al2
-- name    : Formalism.FourierDecayAlt.P.B6.al2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:01:36.997027+00:00
-- url     : https://prove2.me/theorems/ef364371-1b5f-4487-9747-378af957ef19
-- title:
--   B6: al2
-- statement:
--   The B6 construction uses the al2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1789-L1856
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1789-L1856

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

theorem Formalism.FourierDecayAlt.P.B6.al2 {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2)
    (ρ : ℝ) (q : ℕ → ℕ → ℝ → ℝ → ℂ)
    (hy : ∀ l < 2, ∀ x > 0, ∀ y > 0,
      HasDerivAt (fun y' => q 0 l x y') (((-(ρ / y) : ℝ) : ℂ) * q 0 (l + 1) x y) y)
    (hx : ∀ m < 2, ∀ l ≤ 2, ∀ x > 0, ∀ y > 0,
      HasDerivAt (fun x' => q m l x' y) (((-(ρ / x) : ℝ) : ℂ) * q (m + 1) l x y) x)
    (hc : ∀ m ≤ 2, ∀ l ≤ 2, ContinuousOn (fun t : ℝ × ℝ => q m l t.1 t.2) Quad)
    (h : ℝ → ℝ → ℂ) (hh : ∀ x y, h x y = ((W x * W y : ℝ) : ℂ) * q 0 0 x y) :
    (∀ x y, oneMinusDD h x y = ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
      ((gam ρ W m x * gam ρ W l y : ℝ) : ℂ) * q m l x y) ∧
    (∀ x, ContDiff ℝ 2 (fun y => h x y)) ∧
    (∀ y, ContDiff ℝ 2 (fun x => h x y - iteratedDeriv 2 (fun y' => h x y') y)) ∧
    (∀ x₁ x₂ : ℝ, (∫ t : ℝ × ℝ, oneMinusDD h t.1 t.2 *
        Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      (((1 + x₁ ^ 2) * (1 + x₂ ^ 2) : ℝ) : ℂ) *
        ∫ t : ℝ × ℝ, h t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) := by sorry
