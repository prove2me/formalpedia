-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_C1_full_atom_grid_terminal_reserve_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_canonical_C1_full_atom_grid_terminal_reserve_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:07:17.945199+00:00
-- url     : https://prove2.me/theorems/8d47583e-278d-4c25-b9ae-9459994a1f83
-- title:
--   Exact original BV complete atom and discounted finite-grid cash plus terminal physical reserve envelope
-- statement:
--   For the genuine spectrally negative Levy BV reserve and its original initial atom and full right-dividend grid, the canonical positive-cap C1 gradient gives candidate value at least w(0) plus the actual post-payment reserve at every grid endpoint. Combining that pointwise estimate with the already Proved canonical full-atom finite-grid HJB cash budget yields a stopped-grid envelope retaining physical reserve and w(0), without extra nonnegativity assumptions or a surrogate process.
-- source:
--   Source-specific endpoint strengthening of Proved 55d9d542-b965-4f7a-9a5b-125bc7098bfc using Proved f138f64f-f82c-4fdc-943c-d77f480ba88f, original exact rightLimit D and X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_C1_compact_full_atom_grid_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_canonical_C1_full_atom_grid_terminal_reserve_envelope
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
            (w 0 + (x + X.X (u n) ω - rightLimit D (u n) ω)) ≤
          w x +
          (∑ i ∈ Finset.range n,
            Real.exp (-(q * (u (i + 1) : ℝ))) *
              (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by sorry
