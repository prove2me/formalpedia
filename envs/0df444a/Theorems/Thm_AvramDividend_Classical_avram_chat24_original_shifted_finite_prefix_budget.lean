-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_original_shifted_finite_prefix_budget
-- name    : AvramDividend.Classical.avram_chat24_original_shifted_finite_prefix_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:12:08.071082+00:00
-- url     : https://prove2.me/theorems/1a64407a-f33a-4531-a4a1-dec7daeee51a
-- title:
--   Original positive-shift arbitrary finite-grid budget
-- statement:
--   Source-faithful semantic dependency of f8123fbf-cb94-45e8-aca8-e21f50ba9d61, extracted from its complete proof bundle. Combine the original dividend secants, exact discounted finite telescoping and the exponential modulus to bound every monotone finite-grid strict-prefix cash sum plus the pre-right-payment shifted terminal, with error q times mesh times total original dividends. This is a finite theorem and assumes no arbitrary-grid limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Finset AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_chat24_original_shifted_finite_prefix_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (x δ q : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ)
    (hs : ContDiffOn ℝ 1 w (Ioi 0)) (hg : ∀ y > 0, 1 ≤ deriv w y)
    (hδ : 0 < δ) (hq : 0 ≤ q) (ω : Ω) (u : ℕ → ℝ≥0)
    (hu : Monotone u) (hu0 : u 0 = 0) (n : ℕ) (mesh : ℝ)
    (hwidth : ∀ i < n, (u (i + 1) : ℝ) - (u i : ℝ) ≤ mesh)
    (hstop : (u n : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let U : ℕ → ℝ := fun i => riskProcess X x D (u i) ω + δ
    let Z : ℕ → ℝ := fun i => x + δ + X.X (u (i + 1)) ω - D (u i) ω
    (∑ i ∈ range n, e i * (D (u (i + 1)) ω - D (u i) ω)) + e n * w (U n) ≤
      w (x + δ) + (∑ i ∈ range n,
        ((e (i + 1) - e i) * w (U i) + e (i + 1) * (w (Z i) - w (U i)))) +
        q * mesh * D (u n) ω := by sorry
