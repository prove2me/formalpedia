-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a30_original_interval_lindeberg_finset
-- name    : AvramDividend.Classical.avram_ga_a30_original_interval_lindeberg_finset
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T21:58:38.959336+00:00
-- url     : https://prove2.me/theorems/dcd307cc-bd23-4f6a-80e2-ef9dba440ab5
-- title:
--   Original Gaussian finite interval mesh has quantified large-increment quadratic energy bound
-- statement:
--   The expected sum of the large centred Gaussian increment quadratic energies over a finite set of original-process time intervals is bounded by their quantitative source fourth-moment sums.
-- source:
--   Direct root-connected positive-only Gaussian Taylor mesh Lindeberg continuation from ga_a29 for b0d9951c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a30_original_interval_lindeberg_finset
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (I : Finset ι) (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (a b : ι → ℝ≥0) (htime : ∀ i ∈ I, a i ≤ b i)
    (hProxy : ∀ i ∈ I, Measurable (fun ω : Ω =>
      (X.X (b i - a i) ω - ((b i - a i : ℝ≥0) : ℝ) * X.c) / X.σ))
    (hZ : ∀ i ∈ I, Measurable (fun ω : Ω =>
      ((X.X (b i) ω - X.X (a i) ω) -
        ((b i - a i : ℝ≥0) : ℝ) * X.c) / X.σ))
    (r : ℝ) (hr : 0 < r) :
    let Z : ι → Ω → ℝ := fun i ω =>
      ((X.X (b i) ω - X.X (a i) ω) -
        ((b i - a i : ℝ≥0) : ℝ) * X.c) / X.σ
    (∫⁻ ω, ∑ i ∈ I,
       ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ∂P) ≤
    ∑ i ∈ I, ENNReal.ofReal (1 / r ^ 2) *
      ENNReal.ofReal (3 * (((b i - a i : ℝ≥0) : ℝ) ^ 2)) := by sorry
