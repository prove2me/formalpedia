-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChartIntegralLocal_step_loc
-- name    : Formalism.FourierDecayAlt.P.ChartIntegralLocal.step_loc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:31:10.795807+00:00
-- url     : https://prove2.me/theorems/246644f9-e92e-4048-9369-3c08c6d6bab9
-- title:
--   Chart Integral Local: step loc
-- statement:
--   The Chart Integral Local construction uses the step loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChartIntegralLocal.lean#L16-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChartIntegralLocal.lean#L16-L52

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChartIntegralLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem Formalism.FourierDecayAlt.P.ChartIntegralLocal.step_loc {b : Bool} {X : Mat k r} (hX : inLie k r X) (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1)
    (hψm : AEStronglyMeasurable ψ μ) (G : α → Mat k r → E) (hG1 : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G ξ))
    {g : Mat k r} (hg : g ∈ GV k r) {ε : ℝ} (hε : 0 < ε)
    (hGm : ∀ t ∈ Metric.ball (0 : ℝ) ε, AEStronglyMeasurable (fun ξ => G ξ (cv b X t g)) μ)
    (hG'm : AEStronglyMeasurable (fun ξ => op b X (G ξ) g) μ)
    (β : α → ℝ) (hβ : Integrable β μ)
    (hb0 : ∀ ξ, ‖G ξ g‖ ≤ β ξ) (hb1 : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ ξ, ‖op b X (G ξ) (cv b X t g)‖ ≤ β ξ)
    (Φ : Mat k r → E) (hΦ : ∀ t ∈ Metric.ball (0 : ℝ) ε, Φ (cv b X t g) = ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ) :
    op b X Φ g = ∫ ξ, ψ ξ • op b X (G ξ) g ∂μ := by sorry
