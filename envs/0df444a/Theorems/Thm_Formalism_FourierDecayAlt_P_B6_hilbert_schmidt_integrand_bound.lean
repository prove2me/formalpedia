-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hilbert_schmidt_integrand_bound
-- name    : Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_integrand_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:56:42.438+00:00
-- url     : https://prove2.me/theorems/a685811a-4c0b-4c9b-854e-3b41b21d4383
-- title:
--   B6: hilbert schmidt integrand bound
-- statement:
--   The B6 construction uses the hilbert schmidt integrand bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L941-L948
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L941-L948

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

theorem Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_integrand_bound (D : RealPlaceData k r Wp Wq) (A B : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r}
    (hp : D.inSS p) (g : Mat k r) :
    ‖hsInner (rho D p A g) (B g)‖ ≤ (Module.finrank ℂ Wq : ℝ) *
      (‖A ((Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ * ‖B g‖) := by sorry
