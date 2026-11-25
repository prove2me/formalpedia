-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_low
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_ph_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:16.435823+00:00
-- url     : https://prove2.me/theorems/01013df3-ee5d-472c-804a-ff43a5e079ad
-- title:
--   Stationary Phase Model: E ph low
-- statement:
--   The Stationary Phase Model construction uses the E ph low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2058-L2091
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2058-L2091

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_ph_low {d : ℕ} {φ : (Fin d → ℂ) → ℝ} {n : ℕ} (h3n : 3 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ c₁ ρ : ℝ}
    (hr : 0 < r) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ)
    (hl : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|)
    (hρr : ρ ≤ r) (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n * ρ ≤ c₁ / 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) ρ, ∃ l : Fin d × Bool,
      c₁ / 2 * ‖x‖ ≤ |fderiv ℝ (fun y => quad φ y + s * E_P φ y) x (dirv l)| := by sorry
