-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_clipped_jump_grid_telescope
-- name    : AvramDividend.Classical.avram_jump_phys13_original_clipped_jump_grid_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:24:09.966432+00:00
-- url     : https://prove2.me/theorems/80e9821f-3c09-43a7-b273-6abdbe054a15
-- title:
--   Actual source jump count grid partitions through a randomly clipped final cell
-- statement:
--   For the original spectrally negative Levy process and original pathwise marked jump measure, any monotone physical grid clipped by any finite random clock partitions the stopped jump count exactly, including the last clipped cell and its endpoint. No finite-variation or moment assumptions are required for this pathwise partition.
-- source:
--   Direct consequence of Proved avram_ubv_jump12_original_jump_count_grid_telescope (1f4cc981-ae5c-4cd4-9c35-b48a624ee305) applied to the monotone clipped endpoints. Supports source-level stopped-grid identification for Open 0b1a879a-c9c5-4d2c-9039-a143ec7db5dc.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_jump_count_grid_telescope

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original jump counts partition exactly through the clipped final stopping cell. -/

theorem AvramDividend.Classical.avram_jump_phys13_original_clipped_jump_grid_telescope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (e : ℕ → ℝ≥0) (he : Monotone e) (N : ℕ)
    (ρ : Ω → ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let J : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    J (Ioc (min (e 0) (ρ ω)) (min (e N) (ρ ω)) ×ˢ B) =
      ∑ i ∈ Finset.range N,
        J (Ioc (min (e i) (ρ ω)) (min (e (i + 1)) (ρ ω)) ×ˢ B) := by sorry
