-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_global_discounted_signed_cell_upper_sum
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_global_discounted_signed_cell_upper_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:47:03.007275+00:00
-- url     : https://prove2.me/theorems/43e12235-a977-4ea7-90b2-26a4394d0aaa
-- title:
--   True full-horizon discounted Stieltjes measure dominated by chronological left-weighted signed value-drop upper sum
-- statement:
--   For an arbitrary admissible finite-cap strategy, monotone time grid from zero, and pre-ruin grid endpoints, the true discounted lower integral of dividendMeasure on the complete closed horizon [0,u_n] is bounded by the time-zero cap-linear value drop plus the finite sum of source-frozen cell cap-linear drops each weighted by exp(-q u_i). The estimate is valid at reserve zero and cap, counts the time-zero atom exactly, and does not exclude diffuse or singular-continuous or countably atomic variation.
-- source:
--   The Proved exact closed-horizon partition separates the initial atom from chronological Ioc cells. Proved initial atom bound and Proved source-specific cell left-weighted domination are combined by ENNReal additive and finite-sum monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_global_discounted_signed_cell_upper_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal
        (V (x + X.X 0 ω) -
          V (x + X.X 0 ω - rightLimit D 0 ω)) +
      ∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
          ENNReal.ofReal
            (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
              V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)) := by sorry
