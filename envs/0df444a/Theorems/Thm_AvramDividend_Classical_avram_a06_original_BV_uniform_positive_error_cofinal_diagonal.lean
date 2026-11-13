-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_uniform_positive_error_cofinal_diagonal
-- name    : AvramDividend.Classical.avram_a06_original_BV_uniform_positive_error_cofinal_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:56:30.321204+00:00
-- url     : https://prove2.me/theorems/ec738055-aa59-4872-9aad-4111866016f5
-- title:
--   Original BV physical-grid error admits a cofinal diagonal with vanishing positive expected mass
-- statement:
--   For the true original spectrally negative Lévy process X under its Standing and BV assumptions, arbitrary admissible dividend D, and any finite physical horizon T, there exists a strictly increasing spatial localisation index κ(n) at least n so that the genuine original prepayment reserve n-th physical grid-row exceptional-band error has integrable positive part and vanishing expected positive part along κ(n). The source error is zero on the actual interior compact-band event and otherwise equals the original integrable BV source-mass envelope. This combines two already Proved theorems and supplies the physically adapted two-scale positive error needed in the stopped mesh ledger, without demanding integrability of signed HJB residual.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_positive_error_L1_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_monotone_diagonal_mean
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_BV_uniform_positive_error_cofinal_diagonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k)) :
    let Err : ℕ → ℕ → Ω → ℝ := fun n k ω =>
      if ∀ i < n + 1,
        (0 < Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
        Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
            ∈ Icc (a k) (b k) then (0 : ℝ)
          else |X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|
    ∃ κ : ℕ → ℕ, StrictMono κ ∧ (∀ n, n ≤ κ n) ∧
      (∀ n, Integrable (fun ω => max (Err n (κ n) ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n (κ n) ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
