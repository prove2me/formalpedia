-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:01:18.03851+00:00
-- url     : https://prove2.me/theorems/ed9de935-bfdb-4622-806d-2bf785db782e
-- title:
--   Actual full closed-horizon original-source discounted dividend Stieltjes measure bounded by cap-linear grid drops
-- statement:
--   For a genuine spectrally negative Levy source and admissible finite-cap dividend strategy, every finite monotone pre-ruin time grid starting at zero gives a boundary-safe bound on the single original exponentially discounted dividendMeasure lower integral over the entire closed horizon [0,u_n]. Its upper bound is the cap-linear value decrease at the true time-zero right-payment, plus a sum of cap-linear value decreases on the full subsequent intervals with source values frozen after their chronological left jumps at right endpoints. The actual measure contains all absolutely continuous and singular-continuous dividends and countably many right-payment jumps. No strict-interior localisation, boundary derivative, or purely atomic assumption is needed.
-- source:
--   Combine Proved exact full discounted finite-grid source-specific budget 26939d14-cb58-41f0-8c09-62dd82325825 and the supported new closed-horizon partition lemma avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact. Rewriting the initial singleton and the disjoint cells gives the actual single closed-horizon integral without approximation or loss of the time-zero atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_exact_discounted_all_cells_budget

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    :
    (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (
      (if x + X.X 0 ω ≤ c then w (x + X.X 0 ω)
        else w c + (x + X.X 0 ω - c)) -
      (if x + X.X 0 ω - rightLimit D 0 ω ≤ c
        then w (x + X.X 0 ω - rightLimit D 0 ω)
        else w c + ((x + X.X 0 ω - rightLimit D 0 ω) - c))) +
    ∑ i ∈ Finset.range n,
      ENNReal.ofReal (
        (if x + X.X (u (i + 1)) ω - rightLimit D (u i) ω ≤ c
          then w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)
          else w c +
            ((x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) - c)) -
        (if x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω ≤ c
          then w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
          else w c +
            ((x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) - c))) := by sorry
