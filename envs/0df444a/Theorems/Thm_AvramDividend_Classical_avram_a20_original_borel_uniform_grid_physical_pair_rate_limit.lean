-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_uniform_grid_physical_pair_rate_limit
-- name    : AvramDividend.Classical.avram_a20_original_borel_uniform_grid_physical_pair_rate_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:14:35.45822+00:00
-- url     : https://prove2.me/theorems/e930bcd5-5709-47df-ae6c-f9fc7d20f1f4
-- title:
--   Original arbitrary Borel physical uniform-grid chronological pair expected rates converge to half the squared Lévy intensity
-- statement:
--   For any original spectrally negative Lévy process and any measurable Borel mark set with finite Lévy mass, the exact expected sum across uniform time-grid cells of actual original past-marked counts times subsequent marked-cell counts converges to one half of (T ν(B)) squared. Each finite-grid mean equals the original physical source intensity product sum by the separately Proved arbitrary-Borel grid-pair theorem; the existing Proved uniform NNReal rate triangle reduces that sum to a universal numerical formula; and the independently Proved finite Borel quadratic-rate limit establishes convergence. No Poisson count law, factorial moment assumption or replacement probability space is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_uniform_grid_physical_pair_rate_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hν : X.ν B < ⊤) :
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let A : ℕ → ℝ≥0∞ := fun k =>
      ∫⁻ ω, ∑ i : Fin k,
        N 0 (((i.val : ℝ≥0) * T) / (k : ℝ≥0)) ω *
        N (((i.val : ℝ≥0) * T) / (k : ℝ≥0))
          ((((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)) ω ∂P
    Tendsto A atTop
      (𝓝 ((((T : ℝ≥0∞) * X.ν B) ^ 2) / 2)) := by sorry
