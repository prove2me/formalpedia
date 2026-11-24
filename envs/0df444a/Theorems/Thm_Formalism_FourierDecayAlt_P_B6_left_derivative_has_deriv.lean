-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_left_derivative_has_deriv
-- name    : Formalism.FourierDecayAlt.P.B6.left_derivative_has_deriv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:17:00.322566+00:00
-- url     : https://prove2.me/theorems/b5bf29db-3661-457c-911f-99c9a4f01375
-- title:
--   B6: left derivative has deriv
-- statement:
--   The B6 construction uses the left derivative has deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L648-L662
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L648-L662

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.B6.left_derivative_has_deriv {f f' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g : Mat k r} (hgU : g ∈ U)
    (hg : g ∈ GV k r) (hf' : DifferentiableAt ℝ f' g) (he : ∀ x ∈ U, x ∈ GV k r → f x = f' x) :
    HasDerivAt (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X0 k r)) * g))
      (fderiv ℝ f' g (-(X0 k r * g))) 0 := by sorry
