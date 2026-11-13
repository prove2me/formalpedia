-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_grid_pair_rate_sum_exact
-- name    : AvramDividend.Classical.avram_a20_original_borel_grid_pair_rate_sum_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:38:05.093288+00:00
-- url     : https://prove2.me/theorems/8eb4abfa-7ca0-458d-a977-079515dcd10f
-- title:
--   Exact original arbitrary Borel chronological grid-pair expected rate sum
-- statement:
--   On the original physical spectrally negative Lévy source, every finite deterministic family of past and subsequent Borel-marked rectangles has expected sum of their physical pair-count products equal to the finite sum of the products of their original source ν rates. Sum integrability follows from the Proved measurability of each genuine original marked rectangle count and Mathlib finite-sum lintegral identity. Apply the independently Proved arbitrary-Borel past–future physical count product theorem cell by cell. This generalises the previous full negative cutoff grid-pair rate theorem to every Borel mark set, supplying the finite-grid input for the arbitrary Borel factorial source leaf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_grid_pair_rate_sum_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0)
    (hst : ∀ i, s i ≤ t i)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
      ∑ i : Fin m, ((s i : ℝ≥0∞) * X.ν B) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
