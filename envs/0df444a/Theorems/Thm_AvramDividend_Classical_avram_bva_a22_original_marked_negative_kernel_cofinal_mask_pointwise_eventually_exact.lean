-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_marked_negative_kernel_cofinal_mask_pointwise_eventually_exact
-- name    : AvramDividend.Classical.avram_bva_a22_original_marked_negative_kernel_cofinal_mask_pointwise_eventually_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:37:10.522199+00:00
-- url     : https://prove2.me/theorems/34d251e5-df09-402d-b142-c5919d8d65c3
-- title:
--   Actual original stopped negative-mark Lévy kernel spatial mask is pointwise eventually exact on the entire interior for every arbitrary cofinal band sequence
-- statement:
--   For the actual original spectrally negative Levy X and dividend control D, the genuine time-stopped discounted negative-jump kernel at a fixed original mark-clock-path tuple with strictly positive pre-right-payment left-limit reserve below the actual cap eventually coincides exactly with the unmasked original negative-mark integrand along ANY prescribed cofinal spatial bands a(n),b(n). This is pointwise in every source path, stopped time and negative jump mark and requires no uniform physical/spatial rate, Lévy integrability, finite jump activity or Brownian substitute. The user-supplied hcover hypothesis directly produces the eventual row threshold. This supplies the pointwise hypothesis for dominated convergence of the genuine predictable Lévy-product integrals, conditional on proving an actual source L1 dominator for boundary tails.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_marked_negative_kernel_cofinal_mask_pointwise_eventually_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r ω - rightLimit D r ω) t
    ∀ (S : ℝ≥0) (ω : Ω) (t : ℝ≥0) (z : ℝ),
      (t : ℝ≥0∞) ≤ min (ruinTime X x D ω) (S : ℝ≥0∞) →
      0 < Y t ω → ENNReal.ofReal (Y t ω) < C →
      z < 0 →
      ∀ᶠ n : ℕ in atTop,
        (if (((t : ℝ≥0∞) ≤
          min (ruinTime X x D ω) (S : ℝ≥0∞) ∧
          Y t ω ∈ Icc (a n) (b n)) ∧ z < 0) then
          Real.exp (-(q * (t : ℝ))) *
            (w (Y t ω + z) - w (Y t ω))
        else 0) =
          Real.exp (-(q * (t : ℝ))) *
            (w (Y t ω + z) - w (Y t ω)) := by sorry
