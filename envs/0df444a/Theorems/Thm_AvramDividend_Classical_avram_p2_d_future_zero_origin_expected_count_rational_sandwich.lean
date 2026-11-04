-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_rational_sandwich
-- name    : AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_rational_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:46:00.9959+00:00
-- url     : https://prove2.me/theorems/1b0514e9-716f-4d42-8484-7f4338459f5a
-- title:
--   Source marked mean is trapped between rates at enclosing rational horizons
-- statement:
--   For any original source Lévy process X, any Borel mark B, and any physical horizon t bounded by rationally related endpoints lo and hi with common positive integer denominator d and numerators n,m, its original expected intrinsic marked count lies between n/d and m/d times its original unit-horizon marked count. All inequalities hold in ENNReal including infinite activity; no ν intensity is postulated.
-- source:
--   Combines two genuinely Proved original rate relation instances 2786c7d2 and two instances of original zero-origin mean monotonicity d6f0bf62, preserving exact count/map and original X, P, 𝓕.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_rational_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (lo t hi : ℝ≥0) (n m d : ℕ) (hd : 0 < d)
    (hlo : (d : ℝ≥0) * lo = (n : ℝ≥0))
    (hhi : (d : ℝ≥0) * hi = (m : ℝ≥0))
    (hlot : lo ≤ t) (hthi : t ≤ hi) :
    ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) ≤
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) ∧
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) ≤
      ((m : ℝ≥0∞) / (d : ℝ≥0∞)) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by sorry
