-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regularised_product_second_derivative
-- name    : Formalism.FourierDecayAlt.P.B6.regularised_product_second_derivative
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:16:26.206057+00:00
-- url     : https://prove2.me/theorems/2605a692-5c92-46c2-a65c-6d3731e3b34a
-- title:
--   B6: regularised product second derivative
-- statement:
--   The B6 construction uses the regularised product second derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1588-L1643
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1588-L1643

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

theorem Formalism.FourierDecayAlt.P.B6.regularised_product_second_derivative {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2)
    (ρ : ℝ) {q0 q1 q2 : ℝ → ℂ}
    (h0 : ∀ t, 0 < t → HasDerivAt q0 (((-(ρ / t) : ℝ) : ℂ) * q1 t) t)
    (h1 : ∀ t, 0 < t → HasDerivAt q1 (((-(ρ / t) : ℝ) : ℂ) * q2 t) t)
    (hc : ContinuousOn q2 (Set.Ioi 0)) :
    ContDiff ℝ 2 (fun t => (W t : ℂ) * q0 t) ∧
    ∀ t, (W t : ℂ) * q0 t - iteratedDeriv 2 (fun t => (W t : ℂ) * q0 t) t =
      (gam ρ W 0 t : ℂ) * q0 t + (gam ρ W 1 t : ℂ) * q1 t + (gam ρ W 2 t : ℂ) * q2 t := by sorry
