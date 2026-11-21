-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_original_strict_stopped_prefix_rightdividend_atoms_le_clock
-- name    : AvramDividend.Classical.avram_agentB_original_strict_stopped_prefix_rightdividend_atoms_le_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:24:30.185742+00:00
-- url     : https://prove2.me/theorems/ab8d9057-f404-49b6-88b5-b29e65cae401
-- title:
--   True pre-stop original dividend-atom grid prefix mass bounded by cumulative dividends at the actual stopping clock
-- statement:
--   For the genuine original stochastic dividend strategy and an increasing finite physical grid lying strictly before any sample-path stopping time rho, the total actual right-payment atom mass on that grid is bounded by D(rho)−D(s0), hence uses the real pre-stopped total dividend variation rather than a possibly uncontrolled postruin value D(n). Combine the already Proved genuine grid telescope with the original strict earlier right-limit comparison rightLimit D(s_m)≤D(rho), and D(s_m)≤rightLimit D(s_m). This is a sharper source-exact stopped physical grid mass bound for the Gaussian gradient right-atom estimate.
-- source:
--   Proved avram_agentB_true_original_rightdividend_grid_atoms_telescope, avram_gledger87_original_strict_rightlimit_le_later_dividend, dividendStrategy_le_rightLimit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_agentB_original_strict_stopped_prefix_rightdividend_atoms_le_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s : ℕ → ℝ≥0)
    (hstrict : ∀ i, s i < s (i + 1))
    (m : ℕ) (ρ : ℝ≥0) (hbefore : s m < ρ) :
    (∑ i ∈ Finset.range m,
      (rightLimit D (s i) ω - D (s i) ω)) ≤
      D ρ ω - D (s 0) ω := by sorry
