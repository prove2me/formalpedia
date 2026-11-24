-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_step_int
-- name    : Formalism.FourierDecayAlt.P.Ux10.step_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:36.134406+00:00
-- url     : https://prove2.me/theorems/7c7988c6-dc56-4af0-b83f-5d7db3f07c29
-- title:
--   Ux10: step int
-- statement:
--   The Ux10 construction uses the step int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L763-L797
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L763-L797

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

theorem Formalism.FourierDecayAlt.P.Ux10.step_int {b : Bool} {X : Mat k r} (hX : inLie k r X) [CompleteSpace E] (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1)
    (hψm : AEStronglyMeasurable ψ μ) (G : α → Mat k r → E) (hG1 : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G ξ))
    (hGm : ∀ g ∈ GV k r, AEStronglyMeasurable (fun ξ => G ξ g) μ) (β : α → ℝ) (hβ : Integrable β μ)
    (hb0 : ∀ g ∈ GV k r, ∀ ξ, ‖G ξ g‖ ≤ β ξ) (hb1 : ∀ g ∈ GV k r, ∀ ξ, ‖op b X (G ξ) g‖ ≤ β ξ)
    (Φ : Mat k r → E) (hΦ : ∀ g ∈ GV k r, Φ g = ∫ ξ, ψ ξ • G ξ g ∂μ) :
    ∀ g ∈ GV k r, op b X Φ g = ∫ ξ, ψ ξ • op b X (G ξ) g ∂μ := by sorry
