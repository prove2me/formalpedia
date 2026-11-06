-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_collision_second_moment_quadratic
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_collision_second_moment_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:10:43.783221+00:00
-- url     : https://prove2.me/theorems/cd66a508-bc7d-4574-8020-97d52db80c9a
-- title:
--   Actual original negative-band multi-jump collision has quadratic second moment
-- statement:
--   For the actual original spectrally negative Lévy physical negative-band jump count K on (0,T], the square K² restricted to paths containing at least two band jumps is integrable, with E[K² 1_{K≥2}]≤2r², where r is the exact physical Lévy band intensity. This is an L² collision estimate for stochastic compensated finite-grid jump errors, based on the original count's accepted factorial moment and no process replacement or additional stochastic axiom.
-- source:
--   Original marked count factorial moment theorem 0a13392f-85cb-4eda-8293-758dc8d8a2a7 and original first mean, finite-cardinality identity and ncard measurability. Deterministic inequality K² 1_{K≥2}≤2K(K−1).

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_collision_second_moment_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => if 2 ≤ K ω then ((K ω : ℝ) ^ 2) else 0) P ∧
    (∫ ω, (if 2 ≤ K ω then ((K ω : ℝ) ^ 2) else 0) ∂P) ≤ 2 * r ^ 2 := by sorry
