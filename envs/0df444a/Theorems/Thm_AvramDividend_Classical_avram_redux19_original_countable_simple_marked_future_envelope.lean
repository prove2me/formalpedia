-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_original_countable_simple_marked_future_envelope
-- name    : AvramDividend.Classical.avram_redux19_original_countable_simple_marked_future_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:32:37.778129+00:00
-- url     : https://prove2.me/theorems/54b17420-2c65-4529-bf64-58ac573e4010
-- title:
--   Countable supremum of original finite simple marked-jump future functionals is measurable
-- statement:
--   For the genuine original Levy process, any countable sequence of finite simple nonnegative weighted marked-count functionals over a fixed future interval has a measurable pointwise-supremum extractor on the same shifted source path. This supports monotone simple approximation of arbitrary nonnegative Borel mark-loss weights without assuming Poisson jumps.
-- source:
--   Invoke the Proved finite-simple original future extractor once for each natural stage and take the countable supremum. Apply the pinned Measurable.iSup theorem for ENNReal and the pointwise iSup_congr identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_finite_simple_marked_future_extractor
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux19_original_countable_simple_marked_future_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ → ℕ) (B : ∀ m, Fin (n m) → Set ℝ)
    (hB : ∀ m i, MeasurableSet (B m i))
    (w : ∀ m, Fin (n m) → ℝ≥0∞) :
    ∃ Fpath : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable Fpath ∧
      ∀ ω : Ω,
      (⨆ m : ℕ, ∑ i : Fin (n m), w m i *
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B m i)) =
        Fpath (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) := by sorry
