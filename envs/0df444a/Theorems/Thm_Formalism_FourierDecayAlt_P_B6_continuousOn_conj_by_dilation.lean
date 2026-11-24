-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_conj_by_dilation
-- name    : Formalism.FourierDecayAlt.P.B6.continuousOn_conj_by_dilation
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:01:16.1447+00:00
-- url     : https://prove2.me/theorems/0c3dd51d-9682-4362-9231-b2214ac202cc
-- title:
--   B6: continuous On conj by dilation
-- statement:
--   The B6 construction uses the continuous On conj by dilation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L514-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L514-L523

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.B6.continuousOn_conj_by_dilation (k r : ℕ) (φ : SS k r × (ℝ × ℝ) → Mt k r) (hφ : Continuous φ)
    (ψ : SS k r × (ℝ × ℝ) → ℝ) (hψ : Continuous ψ) (hpos : ∀ q ∈ (Set.univ : Set (SS k r)) ×ˢ Quad, 0 < ψ q) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => conjM (aDil k r (ψ q)) (φ q)) (Set.univ ×ˢ Quad) := by sorry
