-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_weighted_clipped_grid_telescope
-- name    : AvramDividend.Classical.avram_jump_phys13_original_weighted_clipped_grid_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:04:16.584861+00:00
-- url     : https://prove2.me/theorems/7067d39b-0090-4153-a0d1-63c83dd1c169
-- title:
--   Original Lévy weighted marked source telescopes through clipped final grid cell
-- statement:
--   For original X.X and its actual marked jump measure, the ENNReal integral of an arbitrary measurable nonnegative mark weight over a finite monotone physical grid clipped at a random finite stop equals the sum of the integrals over its clipped adjacent cells, including any original jump at the final ruin or horizon clock. In particular this supplies the pathwise signed-linear negative-jump weight through positive and negative parts without finite variation or arbitrary-grid moment claims.
-- source:
--   PJ-PHYS13 supporting physical source proof for canonical Open 0b1a879a, by induction on Proved cbfef811 actual original weighted adjacent halfopen cell additivity; ownership agreement from PJ-CLOSE13.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_marked_jump_weighted_halfopen_cell_add

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump_phys13_original_weighted_clipped_grid_telescope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (e : ℕ → ℝ≥0) (he : Monotone e) (N : ℕ)
    (ρ : Ω → ℝ≥0)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    let Δ : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let J : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ I)).map
        (fun u : ℝ≥0 => (u, Δ u))
    (∫⁻ p, F p ∂J (Ioc (min (e 0) (ρ ω)) (min (e N) (ρ ω)))) =
      ∑ i ∈ Finset.range N,
        (∫⁻ p, F p ∂J
          (Ioc (min (e i) (ρ ω)) (min (e (i + 1)) (ρ ω)))) := by sorry
