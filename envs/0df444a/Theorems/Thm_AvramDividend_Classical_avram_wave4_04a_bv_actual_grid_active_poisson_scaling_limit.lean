-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_grid_active_poisson_scaling_limit
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_grid_active_poisson_scaling_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:54:58.041787+00:00
-- url     : https://prove2.me/theorems/8be1f776-b9c8-4639-880a-1f1fbf7db762
-- title:
--   Actual BV finite-activity Lévy active-grid count converges to Poisson under mesh-rate scaling
-- statement:
--   For the actual finite-negative-activity bounded-variation source spectrally negative Lévy process, take any sequence of deterministic monotone grids with n equal-width cells of width h_n. If the active-cell Bernoulli rate satisfies n(1−exp(−h_n ν((−∞,0))))→r, then the true source probability of exactly k cells exhibiting a strict drift deficit converges to the Poisson mass exp(−r) r^k/k!. This is a genuine source-X grid-count distribution limit, not the Poisson law for actual jump-count measure N_X, and does not assume or assert a source compensator.
-- source:
--   Canonical Proved source BV finite-grid binomial law ebded8db-bbd8-4a6c-9fc4-220f56f7b51e; pinned Mathlib ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop exact remote compiler signature under 0df444a. This is a source-grid-to-Poisson asymptotic step toward, but not a substitute for, an intrinsic jump-count extractor and pathwise count identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_grid_active_count_binomial_ws01b

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_grid_active_poisson_scaling_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℕ → ℕ → ℝ≥0)
    (ht : ∀ n : ℕ, Monotone (t n))
    (h : ℕ → ℝ)
    (hgap : ∀ n i : ℕ, i < n →
      (((t n (i + 1) - t n i : ℝ≥0) : ℝ)) = h n)
    (r : ℝ)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) *
      (1 - Real.exp (-(h n * (X.ν (Iio (0 : ℝ))).toReal))))
      atTop (𝓝 r))
    (k : ℕ) :
    Tendsto (fun n : ℕ =>
      P.real {ω : Ω |
        ((Finset.range n).filter (fun i =>
          X.X (t n (i + 1)) ω - X.X (t n i) ω <
            X.drift * (((t n (i + 1) - t n i : ℝ≥0) : ℝ)))).card = k})
      atTop (𝓝 (Real.exp (-r) * r ^ k / (k.factorial : ℝ))) := by sorry
