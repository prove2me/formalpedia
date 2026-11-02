-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_weighted_full_stieltjes_grid_caplinear_bound
-- name    : AvramDividend.Classical.avram_wave5_04b_weighted_full_stieltjes_grid_caplinear_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:59:13.147204+00:00
-- url     : https://prove2.me/theorems/76630b6d-0e2e-4f51-bd04-5233600b8807
-- title:
--   Full weighted Stieltjes grid, including singular-continuous dividends, has cap-linear frozen-source control on every cell
-- statement:
--   For any finite nondecreasing time grid, any nonnegative cell weights, and arbitrary per-cell frozen source budgets that cover the true right-limit dividend process, the exact weighted integral of all actual Stieltjes dividends on the half-open grid cells is bounded by the sum of the corresponding cap-linear value drops. Every cell contains its absolutely continuous and singular-continuous variation and its right-endpoint dividend atoms. There is no derivative evaluation at reserve zero or the cap, and the source budget may exceed the cap. A separate t=0 atom is treated by the closed-horizon theorem. This is a derivative-free simple-weight approximation building block for the full BV controlled Ito-Meyer argument.
-- source:
--   Proved exact actual dividend simple-grid Stieltjes lintegral 5d51d64e-b975-44a2-b403-36c27b629070; Proved rightLimit monotonicity f7eef805-3be2-4d1e-9ca1-61e09a0f266e; Proved cap-linear full secant 420ddace-18e0-48de-aecc-c7ccbc6c7c52. Direct source-faithful Wave 5 Chat04-B bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightEndpoint_dividendMeasure_simpleGrid_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_weighted_full_stieltjes_grid_caplinear_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hgrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (weight : ℕ → ℝ≥0∞) (y : ℕ → ℝ)
    (hy : ∀ i : ℕ, i < n → rightLimit D (u (i + 1)) ω ≤ y i) :
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i : ℝ) (u (i + 1) : ℝ)).indicator
        (fun _ : ℝ => weight (i + 1)) t
      ∂dividendMeasure D ω) ≤
    ∑ i ∈ Finset.range n,
      weight (i + 1) * ENNReal.ofReal (
        (if y i - rightLimit D (u i) ω ≤ c
          then w (y i - rightLimit D (u i) ω)
          else w c + ((y i - rightLimit D (u i) ω) - c)) -
        (if y i - rightLimit D (u (i + 1)) ω ≤ c
          then w (y i - rightLimit D (u (i + 1)) ω)
          else w c + ((y i - rightLimit D (u (i + 1)) ω) - c))) := by sorry
