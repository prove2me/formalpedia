-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_phase_dilation_deriv_x
-- name    : Formalism.FourierDecayAlt.P.B6.phase_dilation_deriv_x
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:04:30.686356+00:00
-- url     : https://prove2.me/theorems/b389474d-bd25-4f8f-af24-89192297baa3
-- title:
--   B6: phase dilation deriv x
-- statement:
--   The B6 construction uses the phase dilation deriv x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1395-L1433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1395-L1433

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

theorem Formalism.FourierDecayAlt.P.B6.phase_dilation_deriv_x (H : Hyp D Ξ α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hA' : admitted α cA (Ll A)) (hB : admitted α cB B) (hB' : admitted α cB (Ll B)) (dA : DL A) (dB : DL B)
    {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => Ph D A B (dilation₂ (x', y) p))
      (((-(rr r / x) : ℝ) : ℂ) * (Ph D (Ll A) B (dilation₂ (x, y) p) + Ph D A (Ll B) (dilation₂ (x, y) p))) x := by sorry
