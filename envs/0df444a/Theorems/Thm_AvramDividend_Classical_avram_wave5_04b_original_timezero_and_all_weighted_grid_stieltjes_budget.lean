-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_timezero_and_all_weighted_grid_stieltjes_budget
-- name    : AvramDividend.Classical.avram_wave5_04b_original_timezero_and_all_weighted_grid_stieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:16:06.2513+00:00
-- url     : https://prove2.me/theorems/9d91e420-97d6-490d-ad55-70cf68fdb806
-- title:
--   Original Lévy source and actual dividend measure: complete time-zero plus weighted grid all-mass budget
-- statement:
--   The cap-linear boundary-safe control of the entire actual dividendMeasure D omega over the explicit initial atom together with finitely many nondecreasing right-endpoint time cells, with arbitrary nonnegative weights on those cells. The initial closed singleton [0,0] contains the genuine time-zero right-payment atom; each later half-open (u i,u (i+1)] interval contains absolutely continuous dividends, singular-continuous dividends, and terminal right-payment atoms. At each cell, the true Levy source is frozen at the cell's right endpoint, after its left source jump and before the right dividend. No reserve-interior localisation, differentiability at zero/c or purely atomic strategy is assumed. This is a finite-grid interface, not a full moving-source Ito-Meyer theorem.
-- source:
--   Combines Proved 885b5e42-8ccb-409e-ac49-48becc2bf389 at T=0 with source-specific weighted-grid theorem 02437700-0f0c-482e-9562-a3dd49bbc045 by add_le_add; both use actual dividendMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_caplinear_closed_horizon_all_mass_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_weighted_full_stieltjes_grid_bound

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_timezero_and_all_weighted_grid_stieltjes_budget
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
    (hgrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (weight : ℕ → ℝ≥0∞) :
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) +
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i : ℝ) (u (i + 1) : ℝ)).indicator
        (fun _ : ℝ => weight (i + 1)) t
      ∂dividendMeasure D ω) ≤
    ENNReal.ofReal (
      (if x + X.X 0 ω ≤ c then w (x + X.X 0 ω)
        else w c + (x + X.X 0 ω - c)) -
      (if x + X.X 0 ω - rightLimit D 0 ω ≤ c
        then w (x + X.X 0 ω - rightLimit D 0 ω)
        else w c + ((x + X.X 0 ω - rightLimit D 0 ω) - c))) +
    ∑ i ∈ Finset.range n,
      weight (i + 1) * ENNReal.ofReal (
        (if x + X.X (u (i + 1)) ω - rightLimit D (u i) ω ≤ c
          then w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)
          else w c +
            ((x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) - c)) -
        (if x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω ≤ c
          then w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
          else w c +
            ((x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) - c))) := by sorry
