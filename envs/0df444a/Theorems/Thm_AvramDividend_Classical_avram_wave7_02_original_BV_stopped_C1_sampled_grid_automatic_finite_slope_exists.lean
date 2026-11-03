-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_stopped_C1_sampled_grid_automatic_finite_slope_exists
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_stopped_C1_sampled_grid_automatic_finite_slope_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:21:00.911209+00:00
-- url     : https://prove2.me/theorems/0b6e1432-a69a-413a-a6db-addad791f339
-- title:
--   Original BV stopped C1 sampled discounted dividend and time-zero atom budget with a finite slope produced automatically
-- statement:
--   For the exact original controlled spectrally negative Lévy reserve, C1 smoothness on a compact physical positive-cap band yields a finite slope L>=1 without assuming any derivative norm bound, Lipschitz estimate, or cap openness separately. The genuine sampled chronological stopped dividend budget includes the time-zero right-payment atom, all grid increments, the terminal candidate, and the original drift envelope. The actual finite-grid source identity is used; full Stieltjes passage and compensated stochastic limit remain separate.
-- source:
--   Re-publication after remote compiler rejected first attempt only because original dependency theorems abbe600d and f294da35 were Open. Both have now been remotely ACCEPTED and are Proved. Composes the source ENNReal positive-cap openness, automatic compact nnnorm C1 derivative bound, and original finite-grid HJB discounted dividend budget with the time-zero atom. Its conclusion automatically produces finite slope L>=1 for W8-04 without a free compact Lipschitz bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_stopped_C1_sampled_grid_budget_without_free_Lipschitz
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_stopped_C1_sampled_grid_automatic_finite_slope_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C)
    (hBandSmooth : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      u 0 = 0 →
      (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
      (∀ n, 0 ≤ w (x + X.X (u n) ω - rightLimit D (u n) ω)) →
      ∀ n,
        rightLimit D 0 ω +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) +
        Real.exp (-(q * (u n : ℝ))) *
          w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
        w x +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by sorry
