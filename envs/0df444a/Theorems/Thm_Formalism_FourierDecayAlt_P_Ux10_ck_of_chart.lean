-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_ck_of_chart
-- name    : Formalism.FourierDecayAlt.P.Ux10.ck_of_chart
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:26:12.420986+00:00
-- url     : https://prove2.me/theorems/5fe7d84e-db9a-4c23-a665-dcc9c3602d05
-- title:
--   Ux10: ck of chart
-- statement:
--   The Ux10 construction uses the ck of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L853-L883
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L853-L883

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [CompleteSpace E]

theorem Formalism.FourierDecayAlt.P.Ux10.ck_of_chart {F : Mat k r → E} {mm : ℕ}
    (h : ∀ g0 ∈ GV k r, ∃ δ > 0, Metric.ball (0 : J k r → ℝ) δ ⊆ Dom k r ∧
      ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Metric.ball 0 δ)) :
    CkOn ((mm : ℕ) : ℕ∞) (GV k r) F := by sorry
