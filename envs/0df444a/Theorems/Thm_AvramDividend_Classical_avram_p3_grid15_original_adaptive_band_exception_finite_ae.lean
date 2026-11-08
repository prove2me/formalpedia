-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid15_original_adaptive_band_exception_finite_ae
-- name    : AvramDividend.Classical.avram_p3_grid15_original_adaptive_band_exception_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:33:29.880195+00:00
-- url     : https://prove2.me/theorems/8a9b5a97-a05e-461f-8654-8a7c633f6c2a
-- title:
--   Original Lévy adaptive compact bands exclude only finitely many physical grid rows almost surely
-- statement:
--   For the actual controlled Lévy strict prepayment reserve, prescribed positive summable exceptional-probability bounds allow accelerated cofinal spatial bands chosen row by row. By the first Borel-Cantelli lemma, almost every sample has only finitely many physical rows whose interior reserve observation escapes the selected compact band. This supplies the source-exact almost-sure eventual localisation component requested by P3 compensated-grid theorem 0b2da5b3. It does not establish the original cell/contact L1 error or the fixed unaccelerated band diagonal.
-- source:
--   Public Proved fixed-row 61ebbc7a, adaptive diagonal extraction ece174ef (must be Proved before proof submission), and pinned Mathlib MeasureTheory.ae_finite_setOf_mem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid15_original_adaptive_diagonal_cofinal_band_bad_probability_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid15_original_adaptive_band_exception_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hε : ∀ n, 0 < ε n)
    (hεsum : (∑' n, ε n) < ⊤) :
    ∃ κ : ℕ → ℕ,
      (∀ n, n ≤ κ n) ∧
      ∀ᵐ ω ∂P, ({n : ℕ | ω ∈ {ω : Ω | ∀ i < n + 1,
          (0 < Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
            Icc (a (κ n)) (b (κ n))}ᶜ}).Finite := by sorry
