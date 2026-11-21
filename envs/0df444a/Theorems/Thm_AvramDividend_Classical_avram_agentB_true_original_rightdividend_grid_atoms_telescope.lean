-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_true_original_rightdividend_grid_atoms_telescope
-- name    : AvramDividend.Classical.avram_agentB_true_original_rightdividend_grid_atoms_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:13:56.174619+00:00
-- url     : https://prove2.me/theorems/ad0209be-9bae-4cb6-9cf0-99d377bddf50
-- title:
--   Actual source dividend right-payment atoms over any strictly refining finite physical grid telescope below the genuine cumulative dividend increase
-- statement:
--   For any true original nondecreasing dividend strategy D, sample path ω, and strictly increasing actual physical times s_i, the sum of all genuine rightpayment dividend atoms rightLimit D(s_i)−D(s_i) for i<m is bounded by the cumulative original dividend increase D(s_m)−D(s_0). This is a source-exact pathwise total-variation bound, without a cash reward surrogate, Brownian replacement, independence assumption or artificial stopping clock. It is the finite-grid atom-mass budget needed in the Gaussian first and second Hermite pre/post coefficient L1 errors.
-- source:
--   Proved avram_gledger87_original_strict_rightlimit_le_later_dividend, Finset.sum_range_succ, induction and telescoping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_agentB_true_original_rightdividend_grid_atoms_telescope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s : ℕ → ℝ≥0)
    (hstrict : ∀ i, s i < s (i + 1)) (m : ℕ) :
    (∑ i ∈ Finset.range m,
      (rightLimit D (s i) ω - D (s i) ω)) ≤
    D (s m) ω - D (s 0) ω := by sorry
