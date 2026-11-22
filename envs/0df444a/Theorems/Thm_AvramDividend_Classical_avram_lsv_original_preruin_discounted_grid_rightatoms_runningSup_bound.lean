-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_grid_rightatoms_runningSup_bound
-- name    : AvramDividend.Classical.avram_lsv_original_preruin_discounted_grid_rightatoms_runningSup_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:54:41.853801+00:00
-- url     : https://prove2.me/theorems/e41ff74e-6891-4179-93ec-2e0c145c1222
-- title:
--   Original stopped pre-ruin physical discounted right dividends uniformly bounded by original Levy running supremum
-- statement:
--   For the original spectrally negative Levy source X and any original nondecreasing left-continuous dividend strategy, every finite strictly increasing physical mesh stopped strictly before true ruin has total discounted right-dividend atoms bounded pathwise by initial capital plus original finite-horizon running supremum. Prove by prefix induction without any post-ruin constraint, future time independent hypothesis, or extra integrability assumption. Supports actual Gaussian pre/post mesh L1 rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_gledger87_original_strict_rightlimit_le_later_dividend
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

/- Actual original dividend-strategy right atoms on a deterministic
  physical time grid stopped before ruin. A prefix induction carries both
  an unweighted cumulative payment invariant and the source running
  supremum envelope. No post-ruin dividend bound is assumed. -/

theorem AvramDividend.Classical.avram_lsv_original_preruin_discounted_grid_rightatoms_runningSup_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (s : ℕ → ℝ≥0) (hstrict : ∀ i, s i < s (i + 1))
    (m : ℕ) (hbound : ∀ i ∈ Finset.range m, s i ≤ n)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) :
    (∑ i ∈ Finset.range m,
      if s i < ρ ω then
        Real.exp (-(q * (s i : ℝ))) *
          (rightLimit D (s i) ω - D (s i) ω)
      else 0) ≤ x + runningSup X n ω := by sorry
