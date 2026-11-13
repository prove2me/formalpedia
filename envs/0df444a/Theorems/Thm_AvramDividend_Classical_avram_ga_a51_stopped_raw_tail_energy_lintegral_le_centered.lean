-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a51_stopped_raw_tail_energy_lintegral_le_centered
-- name    : AvramDividend.Classical.avram_ga_a51_stopped_raw_tail_energy_lintegral_le_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:13:08.736194+00:00
-- url     : https://prove2.me/theorems/411d4f01-9a2e-494e-8b74-438dea141a2a
-- title:
--   True stopped Gaussian finite-grid raw large-increment expected energy is bounded by centred large-tail energy
-- statement:
--   For any measurable physical finite-grid centred increments under the original random pre-stop mask, a sufficiently small deterministic drift shift makes the expected squared energy on raw large-increment cells no more than four times the centred large-cell energy.
-- source:
--   Actual original Gaussian stopped Taylor b0d9951c raw-source threshold L1 bridge using small deterministic drift a50 and original Lindeberg a41.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a51_stopped_raw_tail_energy_lintegral_le_centered
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ) (s : ℕ → ℝ≥0)
    (ρ : Ω → ℝ≥0) (Z : ℕ → Ω → ℝ)
    (d η : ℝ) (hη : 0 < η) (hd : |d| ≤ η / 2)
    (hMeas : Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s i < ρ ω then
        ENNReal.ofReal (if η / 2 ≤ |Z i ω| then (Z i ω)^2 else 0)
      else 0)) :
    (∫⁻ ω, ∑ i ∈ Finset.range m,
      if s i < ρ ω then
        ENNReal.ofReal
          (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0)
      else 0 ∂P) ≤
    (4 : ℝ≥0∞) * (∫⁻ ω, ∑ i ∈ Finset.range m,
      if s i < ρ ω then
        ENNReal.ofReal (if η / 2 ≤ |Z i ω| then (Z i ω)^2 else 0)
      else 0 ∂P) := by sorry
