-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_nonnegative_mark_simple_lintegral
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_nonnegative_mark_simple_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:20:18.637684+00:00
-- url     : https://prove2.me/theorems/2178e7e3-4ed0-417a-9f14-75e360c28cfa
-- title:
--   Original intrinsic nonnegative mark simple integral equals weighted source jump counts
-- statement:
--   The finite nonnegative simple marked-jump integral against the actual original Levy intrinsic marked jump measure equals the finite sum of original counts on time-mark rectangles weighted by the simple-function coefficients.
-- source:
--   Original marked source jump measure and pinned Mathlib finite sum lintegral and measurable indicator integral identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_nonnegative_mark_simple_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (c : ι → ℝ≥0∞) (ω : Ω) :
    (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc s t ×ˢ B i).indicator (fun _ => c i) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ i ∈ S, c i *
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i) := by sorry
