-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_phase_bounds
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_phase_bounds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:45.959796+00:00
-- url     : https://prove2.me/theorems/dfc6f678-b4af-4283-9584-4e04d033609b
-- title:
--   Diagonal Point Sigma Finite: ns phase bounds
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns phase bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L241-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L241-L284

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_phase_bounds (m q : ℕ)
    (hRel1 : ∀ (D' : ℂ) (x : Fin (m + 1) → ℂ), (∀ k, x k ≠ 0) →
      ‖dg0 D' x‖ ≤ ‖fderiv ℂ (g0 D') x‖ ∧ ‖fderiv ℂ (g0 D') x‖ ≤ ((m : ℝ) + 1) * ‖dg0 D' x‖)
    (Cj : ℕ → ℝ)
    (hCj : ∀ j : ℕ, 1 ≤ j → ∀ (D' : ℂ) (x : Fin (m + 1) → ℂ) (r : ℝ), 0 < r → (∀ k, r ≤ ‖x k‖) →
      ‖iteratedFDeriv ℂ (j + 1) (g0 D') x‖ ≤ Cj j * (1 + ‖dg0 D' x‖) * (r ^ j)⁻¹)
    {cg : ℝ} (hcg : 0 < cg) {D' : ℂ} {x : Fin (m + 1) → ℂ} {r : ℝ} (hr : 0 < r) (hx : ∀ k, r ≤ ‖x k‖)
    (hg : cg ≤ ‖dg0 D' x‖) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    ‖iteratedFDeriv ℂ (j + 1) (g0 D') x‖ ≤
      ‖fderiv ℂ (g0 D') x‖ * ((1 + (∑ i ∈ Finset.range (q + 1), |Cj i|) * (1 + 1 / cg)) / r) ^ j := by sorry
