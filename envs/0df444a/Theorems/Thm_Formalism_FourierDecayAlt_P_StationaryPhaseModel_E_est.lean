-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_est
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_est
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:37.247395+00:00
-- url     : https://prove2.me/theorems/d54d7835-f6f7-45cb-898f-90234b5e990e
-- title:
--   Stationary Phase Model: E est
-- statement:
--   The Stationary Phase Model construction uses the E est property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2122-L2136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2122-L2136

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ : ℝ} {φ : (Fin d → ℂ) → ℝ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_est {q : ℕ} {C : ℝ} (hq : q ≤ 4) (hOB : E_OB d q β (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) C)
    (hr : 0 < r) (hph : E_Phase d r Γ c₁ φ) (hρr : ρ ≤ r)
    (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6) * ρ ≤ c₁ / 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (K : ℝ)
    (hK : 0 ≤ K) (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ Metric.closedBall (0 : Fin d → ℂ) ρ)
    (hb : Sym (Metric.closedBall (0 : Fin d → ℂ) ρ) (wt (Real.sqrt τ)) (2 * (q : ℤ)) (d + 1 + q) K b) :
    ‖∫ x, osc (fun y => quad φ y + s * E_P φ y) τ x • b x ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + q) := by sorry
