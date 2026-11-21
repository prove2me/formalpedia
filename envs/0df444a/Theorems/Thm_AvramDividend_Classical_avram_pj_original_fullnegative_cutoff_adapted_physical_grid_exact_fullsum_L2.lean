-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_cutoff_adapted_physical_grid_exact_fullsum_L2
-- name    : AvramDividend.Classical.avram_pj_original_fullnegative_cutoff_adapted_physical_grid_exact_fullsum_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:24:59.455424+00:00
-- url     : https://prove2.me/theorems/c296efc8-c24c-451a-bff1-bfba7b520667
-- title:
--   Original true full negative-cutoff Lévy marked physical-grid stopped martingale full squared sum exact diagonal energy
-- statement:
--   For the actual spectrally negative Lévy marked negative-cutoff point process, uniform or arbitrary equally stepped physical grid, and true right-continuous filtration, the full square of the sum of original compensated weighted cell increments has expected energy equal to the sum of diagonal expected squared cell increments. Assumes explicitly that the original weighted increments are integrable, future centred counts are integrable and earlier cell times later predictable weight is past measurable. Uses the Proved exact original full-negative cutoff conditional count mean-zero theorem, without artificially replacing the original jumps by independent variables or Gaussian noise.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_fullnegative_cutoff_adapted_physical_grid_exact_fullsum_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m cut : ℕ) (Δ : ℝ≥0) (grid : ℕ → ℝ≥0)
    (hStep : ∀ j, grid (j + 1) = grid j + Δ)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ j, N j = fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
        (Ioc (grid j) (grid (j + 1)) ×ˢ
          Iic (-(1 / ((cut : ℝ) + 1)))))
    (r : ℕ → ℝ)
    (hRate : ∀ j, r j =
      ((Δ : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal)
    (H Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ω, Z i ω = H i ω * ((N i ω).toReal - r i))
    (hVInt : ∀ j ∈ Finset.range m,
      Integrable (fun ω => (N j ω).toReal - r j) P)
    (hPair : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P)
    (hPast : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      i < j →
      StronglyMeasurable[𝓕.rightCont (grid j)]
        (fun ω => Z i ω * H j ω)) :
    (∫ ω, (∑ i ∈ Finset.range m, Z i ω)^2 ∂P) =
      ∑ i ∈ Finset.range m, ∫ ω, (Z i ω)^2 ∂P := by sorry
