-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB60_original_zerojump_two_uniform_grid_energy_bound
-- name    : AvramDividend.Classical.avram_gbB60_original_zerojump_two_uniform_grid_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:16:25.665244+00:00
-- url     : https://prove2.me/theorems/edaa32c6-e78e-41a6-91f1-febea49c2700
-- title:
--   Original zero-jump Gaussian common-refinement energy bound for two unrelated uniform grids
-- statement:
--   For uniformly bounded original-filtration-adapted grid coefficients, refine two unrelated uniform partitions of the same finite horizon to their product mesh. The squared L2 difference of the original Gaussian martingale sums is bounded by the Gaussian variance times the common-refinement mean-square coefficient energy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB60_original_zerojump_two_uniform_grid_energy_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ)
    (hAdapt : ∀ (m i : ℕ),
      Measurable[𝓕.rightCont
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))]
        (G m i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ m i ω, |G m i ω| ≤ B) :
    let L : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        G m i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
          (Δ : ℝ) * X.c))
    let E : ℕ × ℕ → ℝ := fun nm =>
      let m : ℕ := nm.1
      let p : ℕ := nm.2
      let N : ℕ := (m + 1) * (p + 1)
      let Δ : ℝ := (n : ℝ) / (N : ℝ)
      Δ * (Finset.range N).sum (fun i =>
        ∫ ω, (G m (i / (p + 1)) ω -
          G p (i / (m + 1)) ω) ^ 2 ∂P)
    ∀ (m p : ℕ),
      0 ≤ (∫ ω, (L m ω - L p ω) ^ 2 ∂P) ∧
      (∫ ω, (L m ω - L p ω) ^ 2 ∂P) ≤
        X.σ ^ 2 * E (m, p) := by sorry
