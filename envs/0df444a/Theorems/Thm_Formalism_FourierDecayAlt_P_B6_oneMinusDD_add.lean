-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_oneMinusDD_add
-- name    : Formalism.FourierDecayAlt.P.B6.oneMinusDD_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:36.695282+00:00
-- url     : https://prove2.me/theorems/795c14d6-0c3e-45b4-a62d-dda8b868904a
-- title:
--   B6: one Minus DD add
-- statement:
--   The B6 construction uses the one Minus DD add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1528-L1543
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1528-L1543

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

theorem Formalism.FourierDecayAlt.P.B6.oneMinusDD_add {h₁ h₂ : ℝ → ℝ → ℂ} (a₁ : ∀ x, ContDiff ℝ 2 (fun y => h₁ x y))
    (a₂ : ∀ x, ContDiff ℝ 2 (fun y => h₂ x y))
    (b₁ : ∀ y, ContDiff ℝ 2 (fun x => h₁ x y - iteratedDeriv 2 (fun y' => h₁ x y') y))
    (b₂ : ∀ y, ContDiff ℝ 2 (fun x => h₂ x y - iteratedDeriv 2 (fun y' => h₂ x y') y)) (x y : ℝ) :
    oneMinusDD (fun x y => h₁ x y + h₂ x y) x y = oneMinusDD h₁ x y + oneMinusDD h₂ x y := by sorry
