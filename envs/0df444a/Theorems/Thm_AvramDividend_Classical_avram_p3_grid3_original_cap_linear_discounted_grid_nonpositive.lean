-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_cap_linear_discounted_grid_nonpositive
-- name    : AvramDividend.Classical.avram_p3_grid3_original_cap_linear_discounted_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:06:24.125435+00:00
-- url     : https://prove2.me/theorems/b15fa8ad-5c6a-4eae-bd9c-d786a0021b3d
-- title:
--   Canonical original BV cap-linear finite-grid dividend-cell sign, scoped payoffs
-- statement:
--   Valid source-exact original BV Stieltjes cap-linear cell inequality, expressing the cell payoff as a bound let cell function so Lean has correct scope for indices within nested lintegrals. No additional stochastic or boundary hypotheses beyond actual admissibility and any-cap source theorem. Ruin-endpoint cells remain separate.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_discounted_cell_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_cap_linear_discounted_grid_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hu : Monotone u)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let cell : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc ((u i : ℝ≥0) : ℝ) ((u (i + 1) : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (u i : ℝ))) *
        (V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω))
    (∑ i ∈ Finset.range n, cell i) ≤ 0 := by sorry
