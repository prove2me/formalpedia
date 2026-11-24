-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_norm_admissible_of_double_translate_le
-- name    : Formalism.FourierDecayAlt.P.B6.norm_admissible_of_double_translate_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:49.885942+00:00
-- url     : https://prove2.me/theorems/12707a34-c097-4d16-a96c-b2bb4ed3dbcd
-- title:
--   B6: norm admissible of double translate le
-- statement:
--   The B6 construction uses the norm admissible of double translate le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1197-L1208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1197-L1208

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

theorem Formalism.FourierDecayAlt.P.B6.norm_admissible_of_double_translate_le {α c : ℝ} (hα : 0 ≤ α) {f : Mat k r → (Wq →L[ℂ] Wp)} (hf : admitted α c f)
    {u v g : Mat k r} (hu : u ∈ GV k r) (hv : v ∈ GV k r) (hg : g ∈ GV k r) {K : ℝ}
    (h1 : gN u⁻¹ ≤ K) (h2 : gN v⁻¹ ≤ K) :
    ‖f (u * g * v)‖ ≤ c * (K * K) ^ α * gN g ^ (-α) := by sorry
