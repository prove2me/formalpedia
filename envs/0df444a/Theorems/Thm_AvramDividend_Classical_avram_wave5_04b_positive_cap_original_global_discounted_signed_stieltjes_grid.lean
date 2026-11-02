-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_discounted_signed_stieltjes_grid
-- name    : AvramDividend.Classical.avram_wave5_04b_positive_cap_original_global_discounted_signed_stieltjes_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:47:20.591023+00:00
-- url     : https://prove2.me/theorems/f9367805-8711-4ef3-9b8b-371cad80f542
-- title:
--   Uniform positive ENNReal-cap complete discounted Stieltjes dividend closed-grid signed domination with time-zero atom
-- statement:
--   For every positive finite or infinite cap, original admissible strategy and pre-ruin monotone grid, the actual complete discounted dividendMeasure integral on [0,u_n], including the time-zero payment atom, is bounded by the initial value drop plus a sum over chronological half-open cells of left-endpoint exponentially weighted source-frozen cap-linear value drops. Covers diffuse, singular-continuous and countably atomic payments and zero/cap contacts, with no strict interior localisation or finite-cap assumption.
-- source:
--   Combine Proved exact closed-horizon Icc partition, Proved uniform positive-cap T=0 horizon atom budget and Proved uniform positive-cap source-specific left-discounted cell domination by additive and finite-sum monotonicity of ENNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_discounted_full_stieltjes_cell_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_positive_cap_original_global_discounted_signed_stieltjes_grid
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
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal
        (V (x + X.X 0 ω) -
          V (x + X.X 0 ω - rightLimit D 0 ω)) +
      ∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
          ENNReal.ofReal
            (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
              V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)) := by sorry
