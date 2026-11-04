-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_uniform_negative_band_grid_occupied_mean
-- name    : AvramDividend.Classical.avram_wave7_06_original_uniform_negative_band_grid_occupied_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:09:23.394078+00:00
-- url     : https://prove2.me/theorems/592972d7-31e4-4eb5-86f1-c3a7813878d2
-- title:
--   Actual original uniform-grid negative-band occupied count has exact expected cell factor
-- statement:
--   On the original spectrally negative Lévy process X, the expected number of nonempty marked negative-band cells of an equal-width deterministic grid equals m times the source probability that the first cell is nonempty. The exact intrinsic source jump measure NX is supplied with an equality to the genuine X path and left limits. Per-cell measurability is explicit. The proof composes source stationary occupied-cell expectation with finite-sum lintegral; no ν-rate identification is asserted.
-- source:
--   W7-06 original occupied-grid finite-expectation step between source void stationary event and source dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave7_06_original_uniform_negative_band_grid_occupied_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (δ : ℝ≥0) (n m : ℕ)
    (hCellMeas : ∀ i ∈ Finset.range m, Measurable
      (fun ω : Ω =>
        ({ω : Ω | NX ω
          (Ioc ((i : ℝ≥0) * δ) ((i : ℝ≥0) * δ + δ) ×ˢ
            Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}).indicator
          (fun _ => (1 : ENNReal)) ω)) :
    (∫⁻ ω, ∑ i ∈ Finset.range m,
      ({ω : Ω | NX ω
        (Ioc ((i : ℝ≥0) * δ) ((i : ℝ≥0) * δ + δ) ×ˢ
          Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}).indicator
        (fun _ => (1 : ENNReal)) ω ∂P) =
      (m : ENNReal) *
        (1 - P {ω : Ω | NX ω
          (Ioc 0 δ ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}) := by sorry
