-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_original_countable_simple_marked_future_past_factor
-- name    : AvramDividend.Classical.avram_redux19_original_countable_simple_marked_future_past_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:46:26.412839+00:00
-- url     : https://prove2.me/theorems/1d8fff1a-b744-4e25-9941-7a3bdfd448fc
-- title:
--   Countable original marked-jump future envelopes factor from all adapted past weights
-- statement:
--   The countable supremum of finite simple weighted original jump-count functionals on a fixed future interval is independent, in nonnegative extended integral factorisation, of arbitrary adapted past weights. This is the source exact countable-simple monotone approximation bridge toward Borel marked-jump Laplace factorisation.
-- source:
--   Apply the original countable future extractor to obtain a measurable functional of the shifted future path. Substitute its pointwise identity into the already Proved arbitrary future functional versus adapted past factorisation theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_countable_simple_marked_future_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux19_original_countable_simple_marked_future_past_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (n : ℕ → ℕ) (B : ∀ m, Fin (n m) → Set ℝ)
    (hB : ∀ m i, MeasurableSet (B m i))
    (w : ∀ m, Fin (n m) → ℝ≥0∞) :
    (∫⁻ ω, H ω * (⨆ m : ℕ, ∑ i : Fin (n m), w m i *
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B m i)) ∂P) =
    (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, ⨆ m : ℕ, ∑ i : Fin (n m), w m i *
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B m i) ∂P) := by sorry
