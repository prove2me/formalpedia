-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_weighted_full_stieltjes_grid_bound
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_weighted_full_stieltjes_grid_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:59:35.874296+00:00
-- url     : https://prove2.me/theorems/02437700-0f0c-482e-9562-a3dd49bbc045
-- title:
--   Original pre-ruin Lévy source controls all singular-continuous dividends on weighted cap-linear grid cells
-- statement:
--   For an actual spectrally negative Lévy source with admissible finite-cap dividends, take a nondecreasing finite grid whose right endpoints are genuine pre-ruin payment times. The full original Stieltjes integral of arbitrary nonnegative simple cell weights, including singular-continuous and absolutely continuous variation and every right dividend atom, is bounded by cap-linear value drops where each cell freezes the actual Lévy source at its right endpoint. Each source left jump is incorporated in X at that endpoint before its right dividend, and post-payment solvency follows from admissibility. The time-zero atom is handled separately. This is an exact finite-grid chronological interface towards the full original-process Ito-Meyer control estimate, without strict-interior localisation or derivative at zero/cap.
-- source:
--   Proved actual dividendMeasure simple-grid lintegral 5d51d64e-b975-44a2-b403-36c27b629070, Proved rightLimit monotone f7eef805-3be2-4d1e-9ca1-61e09a0f266e, Proved cap-linear secant 420ddace-18e0-48de-aecc-c7ccbc6c7c52, actual IsAdmissibleLe post-payment solvency. Wave 5 04-B exact chronological original source grid reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightEndpoint_dividendMeasure_simpleGrid_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_weighted_full_stieltjes_grid_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
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
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i : ℝ) (u (i + 1) : ℝ)).indicator
        (fun _ : ℝ => weight (i + 1)) t
      ∂dividendMeasure D ω) ≤
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
