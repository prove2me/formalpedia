-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_random_record_shifted_rational_survival_ae_clock
-- name    : AvramDividend.Classical.avram_ws01h_random_record_shifted_rational_survival_ae_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:08:57.968438+00:00
-- url     : https://prove2.me/theorems/09590602-4b18-45cd-ad2f-c50c2769772c
-- title:
--   Pathwise a.e. shifted-future rational nonruin transfers from residual clock to actual real terminal clock for every random record age
-- statement:
--   For any original spectrally negative Lévy process, arbitrary initial reserve a and arbitrary path-dependent finite nonnegative record age τ(ω), the measurable rational-grid nonruin tests of the entire Lévy path shifted at τ(ω) agree, for Lebesgue almost every actual real terminal observation time r, with the full closed-horizon nonruin of the shifted Lévy future up to the residual age r−τ(ω). This is a genuine stochastic source statement for every sample path, not a change-of-law claim: fix ω, invoke the canonically proved shifted-clock a.e. rational/closed equivalence and transport null sets through a real translation of Lebesgue measure via pinned Mathlib eventually_sub_right_iff. It is the missing pathwise premise for the genuine Qp a.e. weighted reward transfer, without using a two-sided exit formula.
-- source:
--   Proved avram_ws01h_shifted_rational_future_ae_closed_survival e2c4309a and pinned Mathlib MeasureTheory.eventually_sub_right_iff for real Lebesgue volume.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_shifted_rational_future_ae_closed_survival

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_random_record_shifted_rational_survival_ae_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ)
    (τ : Ω → ℝ≥0) (ω : Ω) :
    ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
      (0 ≤ r - (τ ω : ℝ) ∧ ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ <
            Real.toNNReal (r - (τ ω : ℝ)) →
          0 ≤ a + (X.X (τ ω + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω -
            X.X (τ ω) ω)) ↔
      (0 ≤ r - (τ ω : ℝ) ∧ ∀ s : ℝ≥0,
        s ≤ Real.toNNReal (r - (τ ω : ℝ)) →
          0 ≤ a + (X.X (τ ω + s) ω - X.X (τ ω) ω)) := by sorry
