-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_original_finite_simple_marked_future_extractor
-- name    : AvramDividend.Classical.avram_redux19_original_finite_simple_marked_future_extractor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:16:29.041321+00:00
-- url     : https://prove2.me/theorems/c1aa9f39-fc90-402d-b49f-231f5372ff2c
-- title:
--   Finite simple weighted original marked-count sums have a measurable same-future-path extractor
-- statement:
--   Every finite simple nonnegative weighting of the original intrinsic marked-jump counts over one finite time window admits a measurable function of the exact same shifted original future path, for arbitrary measurable mark bands and coefficients. This provides the first source-exact simple-function step towards the measurable intrinsic exponential-mark-loss functional.
-- source:
--   Use the Proved per-Borel-band future-path measurable extractor 5cf3e058 for each finite index, choose all measurable functions simultaneously, sum them with fixed nonnegative weights using Finset.measurable_sum, and rewrite the original marked counts term by term.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux19_original_finite_simple_marked_future_extractor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ) (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (w : Fin n → ℝ≥0∞) :
    ∃ Fpath : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable Fpath ∧
      ∀ ω : Ω,
      (∑ i : Fin n, w i *
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B i)) =
        Fpath (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) := by sorry
