-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_stopped_C1_sampled_grid_budget_without_free_Lipschitz
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_stopped_C1_sampled_grid_budget_without_free_Lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:00:52.979808+00:00
-- url     : https://prove2.me/theorems/abbe600d-7997-4e51-bf23-74a2f08dd30b
-- title:
--   Original stopped BV C1 finite-grid time-zero dividend budget with Lipschitz and slope-1 constant constructed from the physical derivative band
-- statement:
--   For the actual original BV spectrally negative Levy X, exact controlled strategy D, zero-time right-payment atom, monotone chronological grid and physical compact positive reserve band, a bounded source C1 derivative supplies its own slope constant max(K,1). The already-Proved exact sampled nonnegative HJB dividend budget then bounds initial atom, discounted grid payments and discounted terminal candidate by the original value plus a physical drift budget. No independent Lipschitz hypothesis is assumed. This is a finite-grid statement; passage to genuine full Stieltjes time and expectation remains separate.
-- source:
--   Source-faithful exact sampled nonnegative chronological dividend grid theorem 1f699f37, with physical C1 compact derivative bound supplying hLip through Proved 82f28985. Explicit K is a genuine derivative norm bound on the original reserve strip. No surrogate process or extraneous dividend clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_discounted_grid_sampled_nonnegative_budget
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_stopped_C1_sampled_grid_budget_without_free_Lipschitz
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
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBandSmooth : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
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
            ((↑(max K 1 : ℝ≥0) : ℝ) * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by sorry
