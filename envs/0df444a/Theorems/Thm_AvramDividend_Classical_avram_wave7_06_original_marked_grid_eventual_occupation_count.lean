-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_marked_grid_eventual_occupation_count
-- name    : AvramDividend.Classical.avram_wave7_06_original_marked_grid_eventual_occupation_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:51:52.256678+00:00
-- url     : https://prove2.me/theorems/d8ff397b-ce06-4158-b52e-f37e0befee59
-- title:
--   Original negative-band marked-count equals fine deterministic-grid occupation eventually on each source path
-- statement:
--   For the exact original Lévy sample path, take the finite source negative-band marked jump-time set S. A sequence of monotone deterministic time grids that covers S and whose maximum cell width tends to zero will, eventually, have exactly one jump per occupied cell. Consequently the genuine original intrinsic jump measure count equals the cardinal of its occupied cells for all sufficiently large grid sizes.
-- source:
--   Exact original Ω, P, X, left limits and negative band; uses accepted source finiteness/card and separate finite-grid geometric proofs, without an auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.avram_wave7_06_original_marked_grid_eventual_occupation_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (k : ℕ)
    (S : Set ℝ≥0)
    (hS : S = {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((k : ℝ) + 1))})
    (grid : ℕ → ℕ → ℝ≥0)
    (hMono : ∀ m, Monotone (grid m))
    (hCover : ∀ m, ∀ u : ℝ≥0, u ∈ S →
      ∃ i : ℕ, i < m ∧ u ∈ Ioc (grid m i) (grid m (i + 1)))
    (hFine : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in (Filter.atTop : Filter ℕ),
        ∀ i < m, (grid m (i + 1) : ℝ) - (grid m i : ℝ) < δ) :
    ∀ᶠ m in (Filter.atTop : Filter ℕ),
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1)))) =
      (((Finset.range m).filter (fun i =>
        ∃ u : ℝ≥0, u ∈ S ∧
          u ∈ Ioc (grid m i) (grid m (i + 1)))).card : ℝ≥0∞) := by sorry
