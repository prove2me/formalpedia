-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_bounded_collision_weighted_L2
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_collision_weighted_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:18:06.102199+00:00
-- url     : https://prove2.me/theorems/ce7fd8b7-db5a-4f34-ab87-ed4fae0992c6
-- title:
--   Original bounded random coefficient collision has a quadratic L2 squared-error bound
-- statement:
--   For the physical original negative-band jump count, every measurable random coefficient with deterministic absolute bound B yields a square-integrable collision-weighted count. Its second moment is at most 2B² times the squared finite-band Lévy intensity. The bound is source-exact and directly prepares L2 estimates for finite-band predictable martingale approximations.
-- source:
--   Depends on the genuine physical squared collision count second moment theorem under current authoring, and exact source ncard measurability. Uses the deterministic |H|≤B bound, measurability and L2 domination.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_collision_weighted_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (H : Ω → ℝ) (hHm : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ ω, |H ω| ≤ B) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω =>
      (H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0)) ^ 2) P ∧
    (∫ ω, (H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0)) ^ 2 ∂P) ≤
      2 * B ^ 2 * r ^ 2 := by sorry
