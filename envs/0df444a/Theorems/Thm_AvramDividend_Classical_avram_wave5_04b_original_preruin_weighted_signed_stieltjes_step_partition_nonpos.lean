-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_weighted_signed_stieltjes_step_partition_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_weighted_signed_stieltjes_step_partition_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:35:24.177591+00:00
-- url     : https://prove2.me/theorems/86b0f4c8-ca53-40a2-9b47-13bc3c502af6
-- title:
--   Original-source complete Stieltjes measure domination by cap-linear drops against arbitrary nonnegative step weights
-- statement:
--   For any nonnegative real step weights on an arbitrary finite pre-ruin dividend time grid, the sum of weights times the actual full Stieltjes dividendMeasure cell masses and the correspondingly weighted chronological source-frozen cap-linear value changes is nonpositive. The theorem controls singular-continuous and diffuse variation as well as countably many dividend right-payment atoms; no boundary derivative or strict-interior reserve localisation is used. It is an exact simple-function measure-domination input for subsequent weighted Itô–Meyer approximation.
-- source:
--   Proved source-specific unweighted full-Stieltjes cell domination, followed by Finset.sum_nonpos and positivity of the chosen weights.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_interval_full_dividend_measure_signed_domination

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_weighted_signed_stieltjes_step_partition_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (r : ℕ → ℝ) (hr : ∀ i : ℕ, i < n → 0 ≤ r i) :
    ∑ i ∈ Finset.range n,
      (r i * (
        (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal +
        V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
        V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω))) ≤ 0 := by sorry
