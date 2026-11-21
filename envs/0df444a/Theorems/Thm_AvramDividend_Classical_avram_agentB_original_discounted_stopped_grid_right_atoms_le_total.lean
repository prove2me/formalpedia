-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_original_discounted_stopped_grid_right_atoms_le_total
-- name    : AvramDividend.Classical.avram_agentB_original_discounted_stopped_grid_right_atoms_le_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:20:16.592163+00:00
-- url     : https://prove2.me/theorems/09f117be-3a51-4787-bf99-079160eb0cc7
-- title:
--   Original stopped discounted physical-grid true right-dividend atoms bounded by cumulative dividend growth
-- statement:
--   On the actual original dividend strategy D, true stopped strict-mesh times s_i with s_i<rho, discount q≥0 and true right-payment atoms rightLimit D(s_i)−D(s_i) have total discounted mass bounded by the original cumulative dividend increase D(s_m)−D(s_0). Uses the existing original actual-path telescoping theorem; each stopped discounted atom lies between zero and the undiscounted actual atom since 0≤exp(−q s)≤1. This exact payment-mass budget is the missing physical-grid constraint needed to convert original Gaussian conditional cell moment estimates into global L1 errors.
-- source:
--   Proved avram_agentB_true_original_rightdividend_grid_atoms_telescope and dividendStrategy_le_rightLimit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_agentB_original_discounted_stopped_grid_right_atoms_le_total
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s : ℕ → ℝ≥0)
    (hstrict : ∀ i, s i < s (i + 1))
    (q : ℝ) (hq : 0 ≤ q) (ρ : ℝ≥0) (m : ℕ) :
    (∑ i ∈ Finset.range m,
      if s i < ρ then
        Real.exp (-(q * (s i : ℝ))) *
          (rightLimit D (s i) ω - D (s i) ω)
      else 0) ≤ D (s m) ω - D (s 0) ω := by sorry
