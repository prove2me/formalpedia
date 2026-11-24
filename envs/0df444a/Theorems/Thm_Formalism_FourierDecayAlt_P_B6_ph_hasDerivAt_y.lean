-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ph_hasDerivAt_y
-- name    : Formalism.FourierDecayAlt.P.B6.ph_hasDerivAt_y
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:03:50.493447+00:00
-- url     : https://prove2.me/theorems/9080ea60-681f-4420-a923-5c2bfb79e94c
-- title:
--   B6: ph has Deriv At y
-- statement:
--   The B6 construction uses the ph has Deriv At y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1355-L1393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1355-L1393

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

theorem Formalism.FourierDecayAlt.P.B6.ph_hasDerivAt_y (H : Hyp D Ξ α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hA' : admitted α cA (Rr A)) (hB : admitted α cB B) (hB' : admitted α cB (Rr B)) (dA : DR A) (dB : DR B)
    {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y' : ℝ => Ph D A B (dilation₂ (x, y') p))
      (((-(rr r / y) : ℝ) : ℂ) * (Ph D (Rr A) B (dilation₂ (x, y) p) + Ph D A (Rr B) (dilation₂ (x, y) p))) y := by sorry
