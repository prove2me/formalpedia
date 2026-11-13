-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a34_original_stopped_mask_large_tail_energy
-- name    : AvramDividend.Classical.avram_ga_a34_original_stopped_mask_large_tail_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:23:40.954275+00:00
-- url     : https://prove2.me/theorems/43d87515-b49b-43f7-adbc-c12c82e0a948
-- title:
--   True stopped Gaussian grid large quadratic increment tail dominated by original fourth energy
-- statement:
--   On the original zero-jump Gaussian process and original probability measure, restricting finite physical Gaussian large-increment quadratic energy to grid starts strictly before an arbitrary stopping clock preserves its fourth-moment expectation bound.
-- source:
--   Actual Gaussian A b0d9951c true pre-stop physical-grid expected positive energy, with no independent-increment assumption on the random clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a34_original_stopped_mask_large_tail_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : 0 < X.σ)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (ρ : Ω → ℝ≥0)
    (hMeas : ∀ i ∈ S, Measurable (fun ω : Ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ))
    (r : ℝ) (hr : 0 < r) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ
    (∫⁻ ω, ∑ i ∈ S,
      if s i < ρ ω then
        ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0)
      else 0 ∂P) ≤
      ENNReal.ofReal (1 / r ^ 2) *
        (∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2)) := by sorry
