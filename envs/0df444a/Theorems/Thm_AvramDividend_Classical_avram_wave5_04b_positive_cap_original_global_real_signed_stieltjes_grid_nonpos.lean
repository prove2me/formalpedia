-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_real_signed_stieltjes_grid_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_positive_cap_original_global_real_signed_stieltjes_grid_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:00:56.919346+00:00
-- url     : https://prove2.me/theorems/680d469d-d6d1-4ae9-ba12-543f1825a206
-- title:
--   Real signed original full discounted Stieltjes dividend correction on complete horizon for any positive cap including infinity
-- statement:
--   For original admissible dividends with any positive ENNReal cap C, the true complete discounted Stieltjes integral on the closed horizon [0,u_n], converted to a real, plus the time-zero V decrease and the sum of source-frozen right-time V decreases weighted by the left-time exponential, is nonpositive. Handles the exact time-zero atom, diffuse and singular-continuous variation, all countably many right-payment jumps, and zero/cap contacts, without a strict-interior reserve assumption or finite-cap restriction.
-- source:
--   Proved uniform source-specific real signed weighted cell inequality, Proved positive-cap closed-horizon budget ensuring finiteness and initial atom correction, Proved positive-cap caplinear/infinite secant at t0, and Proved exact real closed-horizon Stieltjes grid partition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_discounted_cell_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_real_stieltjes_partition_finite
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_positive_cap_original_global_real_signed_stieltjes_grid_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X 0 ω - rightLimit D 0 ω) - V (x + X.X 0 ω)) +
      ∑ i ∈ Finset.range n,
        Real.exp (-(q * (u i : ℝ))) *
          (V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
            V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)) ≤ 0 := by sorry
