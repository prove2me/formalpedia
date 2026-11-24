-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_pint
-- name    : Formalism.FourierDecayAlt.P.Ux10.pint
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:24:59.049669+00:00
-- url     : https://prove2.me/theorems/64ef3d8b-318f-41b6-b28e-af98c5d5a4e9
-- title:
--   Ux10: pint
-- statement:
--   The Ux10 construction uses the pint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L162-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L162-L228

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem Formalism.FourierDecayAlt.P.Ux10.pint {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {U : Set X} (hU : IsOpen U)
    (b : α → ℝ) (hb : Integrable b μ) :
    ∀ (N : ℕ) (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (F : α → X → E'),
      (∀ ξ, ContDiffOn ℝ N (F ξ) U) → (∀ y ∈ U, AEStronglyMeasurable (fun ξ => F ξ y) μ) →
      (∀ i ≤ N, ∀ y ∈ U, ∀ ξ, ‖iteratedFDeriv ℝ i (F ξ) y‖ ≤ b ξ) →
      ContDiffOn ℝ N (fun y => ∫ ξ, F ξ y ∂μ) U ∧
      ∀ i ≤ N, ∀ y ∈ U, ∀ b' : α → ℝ, Integrable b' μ → (∀ ξ, ‖iteratedFDeriv ℝ i (F ξ) y‖ ≤ b' ξ) →
        ‖iteratedFDeriv ℝ i (fun y => ∫ ξ, F ξ y ∂μ) y‖ ≤ ∫ ξ, b' ξ ∂μ := by sorry
