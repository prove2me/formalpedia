-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_uniform_weighted_positive_error_cofinal_diagonal
-- name    : AvramDividend.Classical.avram_a06_original_BV_uniform_weighted_positive_error_cofinal_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T14:51:29.941872+00:00
-- url     : https://prove2.me/theorems/5533aa4d-ccc6-420c-99e4-461273d76660
-- title:
--   A06 physical BV prepayment bad-band positive L1 error vanishes under arbitrary nonnegative row weights
-- statement:
--   For the actual Standing BV spectrally negative Lévy process with admissible dividend D and any finite original horizon, choose cofinal compact spatial cutoff indices κ(n) increasing at least n, such that each bad-band original source mass positive-part error is integrable and the expected error, multiplied by an arbitrary nonnegative row-dependent coefficient 1+L(n), converges to zero. This overcomes growing local C1 derivative and Lipschitz bounds and is an original-process input to the still Open physical stopped cash/HJB ledger.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_positive_error_L1_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_cofinal_weighted_spatial_error_diagonal
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_BV_uniform_weighted_positive_error_cofinal_diagonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n) :
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
      Tendsto (fun n => (1 + L n) *
        ∫ ω, max (Err n (κ n) ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
