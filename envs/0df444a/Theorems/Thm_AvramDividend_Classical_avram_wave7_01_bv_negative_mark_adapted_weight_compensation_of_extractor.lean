-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
-- name    : AvramDividend.Classical.avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:07:25.702934+00:00
-- url     : https://prove2.me/theorems/bb47482c-4294-4845-8598-159248fa0493
-- title:
--   Full-clock original BV negative-jump compensator for arbitrary adapted ENNReal past coefficients
-- statement:
--   For the original Lévy X under BV and explicit finite ν(Iio0), any past-adapted nonnegative extended-real random coefficient H and any physical interval s≤t, the exact intrinsic strictly-negative marked jump count satisfies E[H N_X((s,t]×Iio0)] = E[H] (t−s) ν(Iio0), provided F is a genuinely measurable functional of the original shifted future path equal to this intrinsic count on every original sample. This extends event-indicator compensation to arbitrary unbounded predictable coefficients and time zero, without introducing integrability assumptions or an alternate Poisson model. The extractor remains a stated nontrivial premise.
-- source:
--   Use Proved exact original arbitrary adapted-weight/future-functional ENNReal factor 8a788cbd-318c-4951-a648-5ae463e96084 and the original finite-activity negative-mark rate for all ordered times, then apply pathwise extractor identity in both lintegrals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_original_any_start_negative_mark_exact_rate

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hExtract : ∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) =
      F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
      (∫⁻ ω, H ω ∂P) *
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
