-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_product_integrable
-- name    : Formalism.FourierDecayAlt.P.B6.cutoff_product_integrable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:01:29.650706+00:00
-- url     : https://prove2.me/theorems/34a89274-e7f9-49a5-a42c-90bd4c35e3bb
-- title:
--   B6: cutoff product integrable
-- statement:
--   The B6 construction uses the cutoff product integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1666-L1678
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1666-L1678

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

theorem Formalism.FourierDecayAlt.P.B6.cutoff_product_integrable {v1 v2 : ℝ → ℝ} (hv1 : Continuous v1) (hv2 : Continuous v2)
    (h1 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v1 t = 0) (h2 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v2 t = 0)
    {q : ℝ → ℝ → ℂ} (hq : ContinuousOn (fun t : ℝ × ℝ => q t.1 t.2) Quad) {E : ℝ × ℝ → ℂ} (hE : Continuous E) :
    Integrable (fun t : ℝ × ℝ => ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q t.1 t.2 * E t) := by sorry
