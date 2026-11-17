-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_Borel_physical_count_grid_occupancy_coupling_20261116
-- name    : AvramDividend.Classical.avram_a26_original_Borel_physical_count_grid_occupancy_coupling_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:55:27.175196+00:00
-- url     : https://prove2.me/theorems/c27f305b-c55f-40ec-8355-2cb30824d13e
-- title:
--   Source physical marked-jump count and equal-grid occupied-cell count agree except on quadratic collision event
-- statement:
--   For any positive finite number of equal cells partitioning (0,T], the actual finite-negative-activity physical marked-jump total K equals the number of occupied B-marked cells whenever no cell has two or more jumps. This follows from the original finite marked support and disjoint interval additivity. The probability of disagreement is therefore bounded by the proved source per-cell two-jump bound summed over all cells, O(1/n) for fixed T. This is the finite-grid source coupling needed for the A25 Poisson binomial approximation, without changing Omega or P.
-- source:
--   Source physical marked times finite a.e. c6cc76c9, original source two-jump shifted bound f0852f64, quantitative grid collision helper 92aeb6fa.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_original_Borel_physical_count_grid_occupancy_coupling_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
    let Z : ℕ → Ω → ℕ := fun n ω =>
      ((Finset.range n).filter (fun i : ℕ =>
        NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0)).card
    ∀ n : ℕ, 0 < n →
      (P {ω : Ω | K ω ≠ Z n ω}).toReal ≤
        (n : ℝ) * (((δ n : ℝ≥0∞) * X.ν B).toReal ^ 2 / 2) := by sorry
