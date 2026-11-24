-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_second_derivative_in_y
-- name    : Formalism.FourierDecayAlt.P.B6.second_derivative_in_y
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:05:23.362686+00:00
-- url     : https://prove2.me/theorems/aeff98bc-b546-443a-b39f-df8dd87ba967
-- title:
--   B6: second derivative in y
-- statement:
--   The B6 construction uses the second derivative in y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1728-L1751
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1728-L1751

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

theorem Formalism.FourierDecayAlt.P.B6.second_derivative_in_y {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2)
    (ρ : ℝ) (q : ℕ → ℕ → ℝ → ℝ → ℂ)
    (hy : ∀ l < 2, ∀ x > 0, ∀ y > 0,
      HasDerivAt (fun y' => q 0 l x y') (((-(ρ / y) : ℝ) : ℂ) * q 0 (l + 1) x y) y)
    (hc : ∀ m ≤ 2, ∀ l ≤ 2, ContinuousOn (fun t : ℝ × ℝ => q m l t.1 t.2) Quad)
    (h : ℝ → ℝ → ℂ) (hh : ∀ x y, h x y = ((W x * W y : ℝ) : ℂ) * q 0 0 x y) (x : ℝ) :
    ContDiff ℝ 2 (fun y => h x y) ∧
      ∀ y, h x y - iteratedDeriv 2 (fun y' => h x y') y = regularised_kernel_product ρ W q x y := by sorry
