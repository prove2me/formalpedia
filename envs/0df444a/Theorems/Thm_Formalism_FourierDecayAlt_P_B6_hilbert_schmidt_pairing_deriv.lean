-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hilbert_schmidt_pairing_deriv
-- name    : Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_pairing_deriv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:02:49.738565+00:00
-- url     : https://prove2.me/theorems/3a3a0c36-7264-4b40-b2cb-6b0c4f79e4f2
-- title:
--   B6: hilbert schmidt pairing deriv
-- statement:
--   The B6 construction uses the hilbert schmidt pairing deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1150-L1155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1150-L1155

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

theorem Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_pairing_deriv (L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) {u v : ℝ → (Wq →L[ℂ] Wp)}
    {u' v' : Wq →L[ℂ] Wp} {y : ℝ} (hu : HasDerivAt u u' y) (hv : HasDerivAt v v' y) :
    HasDerivAt (fun s => hsInner (L (u s)) (v s)) (hsInner (L u') (v y) + hsInner (L (u y)) v') y := by sorry
