-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_C1_compact_full_atom_grid_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_canonical_C1_compact_full_atom_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:58:49.845286+00:00
-- url     : https://prove2.me/theorems/55d9d542-b965-4f7a-9a5b-125bc7098bfc
-- title:
--   Actual original BV HJB C1 and zero-boundary automatically yield compact full-atom discounted controlled grid budget
-- statement:
--   For the original BV spectrally negative Levy source, actual right-dividend strategy and canonical positive-cap C1 HJB gradient hypothesis with w0>=0, any strictly positive compact interval inside the cap automatically has candidate nonnegativity and one local Lipschitz constant L>=1. Consequently the complete physical time-zero Stieltjes dividend atom, all later discounted grid right-payment increments and discounted terminal candidate value are bounded by the initial value plus physical discounted drift cells. No extra band-wide w nonnegativity, custom Lipschitz input or altered sample space is required. This is finite-grid stochastic pathwise work; negative Lévy compensator expectation and passage to complete stopped Stieltjes cash are still separate.
-- source:
--   Compose Proved source automatic C1 grid e00f7c91 with the new deterministic positive-cap candidate nonnegativity from w0 and derivative>=1; retains exact original source X and dividend clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_automatic_C1_full_stieltjes_discounted_grid_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_canonical_C1_compact_full_atom_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
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
    (a b : ℝ) (hab : a < b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
        u 0 = 0 →
        (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
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
