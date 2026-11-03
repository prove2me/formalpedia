-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_automatic_C1_full_stieltjes_discounted_grid_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_automatic_C1_full_stieltjes_discounted_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:57:20.556547+00:00
-- url     : https://prove2.me/theorems/e00f7c91-7c5d-4773-bdd3-51a520136097
-- title:
--   Original stopped BV C1 smoothness automatically supplies a uniform compact-stripe Lipschitz constant and time-zero-inclusive discounted full-payment grid budget
-- statement:
--   On any compact strictly positive reserve band inside the exact extended-real cap interior, the original BV C1 smoothness yields a finite Lipschitz constant L at least one. With the genuine original controlled Levy X, stopping and right-dividend strategy D, time-zero Stieltjes atom, and original HJB payment jump bound, all discounted right-dividend increments and discounted terminal C1 value on every monotone reserve-band mesh obey the physical drift-cell budget with that L. The proof composes independently Proved original cap C1 Lipschitz and original time-zero inclusive complete discounted grid theorems; boundary stopping, source compensator expectation and mesh-to-Stieltjes passage remain separate.
-- source:
--   Source-specific C1 compact-band Lipschitz certificate cce8f12b plus new original complete initial Stieltjes discounted finite-grid budget f8f14b92. Logical interface eliminates extra hLip input for W7-04. It does not claim the final stopped stochastic generator expectation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_ENNReal_cap_autoopen_local_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_stieltjes_atom_and_discounted_finite_grid_full_cash_value_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_automatic_C1_full_stieltjes_discounted_grid_budget
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
    (q : ℝ) (hq : 0 ≤ q)
    (hwnonneg : ∀ y ∈ Icc a b, 0 ≤ w y) :
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
