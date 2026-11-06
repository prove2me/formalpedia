-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_bounded_collision_norm_L1
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_collision_norm_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:50:58.873476+00:00
-- url     : https://prove2.me/theorems/3bb11dc1-fc2c-4f51-a8c9-f0241cf7bd81
-- title:
--   Actual original Lévy finite-band collision error has a quadratic weighted L1 norm bound
-- statement:
--   For the original spectrally negative Lévy jump count on (0,T] with threshold -1/(n+1), every measurable bounded random coefficient has an integrable collision-weighted jump count, and its expected absolute value is bounded above by the deterministic coefficient bound times the square of the original band intensity. This is an L1 approximation-error estimate, strengthening the previously accepted bound on the absolute expectation and supporting finite-mesh compensated jump limits.
-- source:
--   Proved/public genuine original-process weighted collision helper 59a94578-6d81-4312-8f6c-b19613f4daef applied to H and |H|, using nonnegativity of physical jump counts.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_collision_norm_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (H : Ω → ℝ) (hHm : Measurable H) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ ω, |H ω| ≤ B) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0)) P ∧
    (∫ ω, ‖H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0)‖ ∂P) ≤ B * r ^ 2 := by sorry
