-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a189_original_stopped_raw_large_tail_ennreal_finset_sum_tendsto
-- name    : AvramDividend.Classical.avram_ga_a189_original_stopped_raw_large_tail_ennreal_finset_sum_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T15:59:13.147198+00:00
-- url     : https://prove2.me/theorems/1b900b47-4af8-4f82-8afc-75c197eca4e0
-- title:
--   Original stopped Gaussian raw large-square tail finite extended sum has vanishing extended expectation
-- statement:
--   For the actual zero-jump Gaussian Lévy source, uniform physical mesh and random stopping clock, the extended nonnegative expectation of the finite sum of real squared raw increments restricted to large events and prefix cells tends to zero. Rewrites the already Proved ga56 raw-plus-drift-centred identity using actual X.X increments. This separates the source probabilistic estimate from the finite real-to-extended sum conversion in a188.
-- source:
--   Original X.X adaptedness and a56 source stopped Gaussian raw tail ENNReal convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a56_original_stopped_raw_large_tail_tendsto
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a189_original_stopped_raw_large_tail_ennreal_finset_sum_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (η : ℝ) (hη : 0 < η) :
    let Tail : ℕ → Ω → ℝ≥0∞ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω then ENNReal.ofReal
          (if η ≤ |r| then r^2 else 0) else 0
    Tendsto (fun m => ∫⁻ ω, Tail m ω ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
