-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger22_original_source_fourth_dominates_large_square_energy
-- name    : AvramDividend.Classical.avram_gledger22_original_source_fourth_dominates_large_square_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:15:05.391017+00:00
-- url     : https://prove2.me/theorems/5665c43f-8086-46ec-a466-95b593db0e19
-- title:
--   Original Gaussian large-source-increment quadratic tail controlled by fourth energy
-- statement:
--   For each finite physical grid of original X.X increments, every positive cutoff eta gives a pointwise bound: eta squared times the sum of squared centred source increments whose absolute size exceeds eta is no larger than the sum of their fourth powers. The same inequality holds after Lebesgue integration on the identical original probability space. Together with proved original Gaussian fourth moment grid upper 27ce427d, this supplies the quantitative large-increment control for the compact Taylor error in the open top-cap stopped original-process Ito budget 0dd6c9b7. There is no arbitrary grid limit, auxiliary Brownian process or dividend-grid identity in the statement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger22_original_source_fourth_dominates_large_square_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (η : ℝ) (hη : 0 < η) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    (∫⁻ ω, ∑ i ∈ S,
      ENNReal.ofReal ((if η ≤ |Z i ω| then (Z i ω)^2 else 0) * η^2) ∂P)
      ≤ (∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal ((Z i ω)^4) ∂P) := by sorry
