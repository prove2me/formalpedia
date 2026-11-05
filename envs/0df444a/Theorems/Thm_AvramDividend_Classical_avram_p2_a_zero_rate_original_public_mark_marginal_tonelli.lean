-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_public_mark_marginal_tonelli
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_public_mark_marginal_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:55:52.713805+00:00
-- url     : https://prove2.me/theorems/7be988cf-faf6-4ae4-8005-e27fa15af24b
-- title:
--   Public original finite-horizon mark marginal and exact nonnegative Tonelli test identity
-- statement:
--   From the public true-original intrinsic jump kernel Tonelli measure, restrict to (0,T] and map time-mark pairs to the mark coordinate. The resulting mark measure is exactly the original mean jump-count measure on every measurable mark set, and its nonnegative test lintegral equals the genuine original sample-space expectation of the time-selected count integral. Uses the pinned map/restrict/lintegral identities, no private P2-D dependency or assumed compensator.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_public_mark_kernel_tonelli
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_public_mark_marginal_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∃ markRate : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        markRate B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∫⁻ y, g y ∂markRate) =
        (∫⁻ ω, ∫⁻ p : ℝ≥0 × ℝ,
          (if p.1 ∈ Ioc (0 : ℝ≥0) T then g p.2 else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) := by sorry
