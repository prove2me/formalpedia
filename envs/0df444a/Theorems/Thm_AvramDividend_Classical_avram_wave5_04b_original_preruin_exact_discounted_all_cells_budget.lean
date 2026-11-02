-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_exact_discounted_all_cells_budget
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_exact_discounted_all_cells_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:42:07.160174+00:00
-- url     : https://prove2.me/theorems/26939d14-cb58-41f0-8c09-62dd82325825
-- title:
--   Original pre-ruin exact exponentially discounted full Stieltjes cells plus time-zero atom
-- statement:
--   On any finite nondecreasing pre-ruin time grid of the actual spectrally negative Levy source and admissible finite-cap dividend strategy, the sum of the genuine exponentially discounted dividendMeasure Stieltjes integrals over each half-open cell, plus the genuine time-zero atom integral, is bounded by corresponding cap-linear value drops computed from the original source at each right endpoint. Every Stieltjes integral retains all absolutely continuous and singular-continuous dividend variation and countably many right-payment jumps, including endpoint cap and zero contacts. The source is evaluated after any left source jump and before the right dividend at the cell endpoint. No artificial stepwise discount approximation, derivative at cap or zero, or strict-interior localisation is required.
-- source:
--   Wave 5 04-B. Proved complete interval Stieltjes budget 02319f55-27be-45a8-a1c2-22a58ed611cb plus Proved genuine original-source initial atom dbaf2f36-1c6c-4d58-aa48-bf08bb84b054. Apply true pre-ruin solvency at each right endpoint, then sum the exact full discount interval estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_caplinear_interval_full_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_exact_discounted_all_cells_budget
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
    :
    (∫⁻ s in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    ∑ i ∈ Finset.range n,
      (∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
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
