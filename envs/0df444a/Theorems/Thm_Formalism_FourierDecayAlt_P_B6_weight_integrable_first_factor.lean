-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_weight_integrable_first_factor
-- name    : Formalism.FourierDecayAlt.P.B6.weight_integrable_first_factor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:05:48.17752+00:00
-- url     : https://prove2.me/theorems/7008a665-067a-473d-b948-9dda61e01e14
-- title:
--   B6: weight integrable first factor
-- statement:
--   The B6 construction uses the weight integrable first factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1957-L1977
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1957-L1977

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

theorem Formalism.FourierDecayAlt.P.B6.weight_integrable_first_factor {Ξ : Mat k r → NNReal} (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r × Mt k r))
    (hm : Measurable fun x : Mt k r => Ξ (Matrix.of x))
    (h : (∫⁻ p : Mt k r × Mt k r, Ξ (Matrix.of p.2 * Matrix.of p.1) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂μ) < ∞) :
    Integrable (fun p : Mt k r × Mt k r => (Ξ (Matrix.of p.2 * Matrix.of p.1) : ℝ) *
      (1 + |lam k r z (Matrix.of p.2)|) ^ (-2 : ℝ)) μ := by sorry
