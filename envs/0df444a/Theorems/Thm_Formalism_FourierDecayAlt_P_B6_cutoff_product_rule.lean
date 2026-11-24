-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_product_rule
-- name    : Formalism.FourierDecayAlt.P.B6.cutoff_product_rule
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:01:02.703006+00:00
-- url     : https://prove2.me/theorems/ebaa8be9-17ff-4ab7-b986-e1664c3a8f5d
-- title:
--   B6: cutoff product rule
-- statement:
--   The B6 construction uses the cutoff product rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1555-L1570
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L1555-L1570

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

theorem Formalism.FourierDecayAlt.P.B6.cutoff_product_rule {u u' : ℝ → ℝ} (hu : ∀ t, HasDerivAt u (u' t) t) (hu0 : ∀ t, t ≤ 0 → u =ᶠ[𝓝 t] 0)
    {q q' : ℝ → ℂ} (hq : ∀ t, 0 < t → HasDerivAt q (q' t) t) (t : ℝ) :
    HasDerivAt (fun t => (u t : ℂ) * q t) ((u' t : ℂ) * q t + (u t : ℂ) * q' t) t := by sorry
