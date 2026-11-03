-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_automatic_C1_grid_sampled_nonnegative_full_atom_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_automatic_C1_grid_sampled_nonnegative_full_atom_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:05:17.063056+00:00
-- url     : https://prove2.me/theorems/2cf48c6a-e45d-4793-b02c-42a285174a1f
-- title:
--   Original BV C1 automatic local Lipschitz with sampled-only nonnegative right-dividend grid and initial physical Stieltjes atom
-- statement:
--   On any compact strictly positive band inside the original extended-real cap, the actual bounded-variation Levy C1 candidate automatically supplies a Lipschitz constant L>=1. For every monotone grid with the actual original postpayment reserve inside that band and nonnegative w at sampled reserve values only, all later discounted right-payment increments plus physical time-zero dividend atom and discounted terminal w obey the local physical drift budget. This is immediately compatible with applying the canonical pre-ruin sampled-value nonnegative hypothesis after localising grids. It uses only independently Proved C1 compact Lipschitz and sampled-positive initial-atom discounted grid source theorems; compensation and full Stieltjes passage remain separate.
-- source:
--   Composition of cce8f12b original cap C1 Lipschitz with new sampled-only time-zero-inclusive discounted cash grid, without global band nonnegativity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_ENNReal_cap_autoopen_local_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_discounted_grid_sampled_nonnegative_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_automatic_C1_grid_sampled_nonnegative_full_atom_budget
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
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hbC : ENNReal.ofReal b ≤ C)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ L : ℝ, 1 ≤ L ∧
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
              (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by sorry
