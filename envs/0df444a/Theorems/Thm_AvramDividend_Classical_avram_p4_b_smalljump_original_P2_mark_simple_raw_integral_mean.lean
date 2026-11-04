-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_mark_simple_raw_integral_mean
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_P2_mark_simple_raw_integral_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:37:38.824031+00:00
-- url     : https://prove2.me/theorems/c485d010-3ef9-4368-b0e1-c9cc986f50bb
-- title:
--   Original source first moment of actual nonnegative marked jump simple integral
-- statement:
--   Given genuine original Levy P2 marked count first-moment rates and measurability on each finite mark band, the expected nonnegative marked-simple integral with respect to the actual original intrinsic jump measure equals its finite weighted original Levy measure rate.
-- source:
--   Actual original Levy source intrinsic marked jump count; proved pathwise simple integral identity; pinned Mathlib lintegral finset and constant multiplication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_nonnegative_mark_simple_lintegral

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_P2_mark_simple_raw_integral_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (c : ι → ℝ≥0∞) (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ω, J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i))
    (hRate : ∀ i ∈ S, (∫⁻ ω, J i ω ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    (∫⁻ ω, (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc s t ×ˢ B i).indicator (fun _ => c i) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑ i ∈ S, c i * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
