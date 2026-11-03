-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_discounted_grid_negative_value_residual_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_initial_atom_discounted_grid_negative_value_residual_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:35:49.374451+00:00
-- url     : https://prove2.me/theorems/6b12ef49-c305-4cd4-b238-8bcce4b1e31f
-- title:
--   Original BV physical time-zero Stieltjes atom and complete discounted grid cash/value with explicit negative candidate-value residual
-- statement:
--   For the genuine original BV controlled Levy source and physical right-dividend measure, the exact time-zero Stieltjes atom plus all subsequent discounted full right-payment increments and discounted terminal w are bounded by w(x), the physical drift grid sum, and the explicit nonnegative negative-part candidate discount residual. This holds without assuming w≥0 on the band or even on sampled states. It combines the signed residual grid source theorem with the Proved exact source time-zero HJB payment atom lemma and leaves source jump compensation and the full stopped Stieltjes limit separate.
-- source:
--   Compose the source signed negative-value residual grid with original exact time-zero Stieltjes atom 0315346e and X.X_zero, with no global or sampled nonnegativity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_discounted_full_payment_grid_negative_value_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_initial_atom_discounted_grid_negative_value_residual_budget
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
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C) (hL1 : 1 ≤ L)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|)
    (q : ℝ) (hq : 0 ≤ q) :
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
            (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) +
        (∑ i ∈ Finset.range n,
          (Real.exp (-(q * (u i : ℝ))) -
            Real.exp (-(q * (u (i + 1) : ℝ)))) *
            max 0 (-(w (x + X.X (u i) ω - rightLimit D (u i) ω)))) := by sorry
