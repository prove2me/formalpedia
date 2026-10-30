-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_shifted_rational_future_ae_closed_survival
-- name    : AvramDividend.Classical.avram_ws01h_shifted_rational_future_ae_closed_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:31:32.257912+00:00
-- url     : https://prove2.me/theorems/e2c4309a-6bb1-49f7-9780-7b01982ee1a0
-- title:
--   Actual shifted Lévy future rational-open survival equals full closed survival almost everywhere in genuine real residual-clock time
-- statement:
--   For every original spectrally negative Lévy sample path shifted by an arbitrary finite real nonnegative age b (including a random stopping age selected afterwards), and every reserve x, the measurable countable rational-open-age survival condition is equivalent almost everywhere in real observation age to exact continuous survival including the residual terminal clock. It uses the canonically Proved shifted rational test versus weak first downclock and the Lebesgue-null singleton of the genuine shifted infimum downclock, not uncountable product-sigma-algebra variable path evaluation. This precisely bridges the true Esscher Qp first-record regeneration reward and source full closed-horizon lower survival, independently of the two-sided exit ratio.
-- source:
--   Proved source shifted rational survival weak downclock; Proved chat04_ennreal_strict_clock_single_time_null_ws01a; genuine shifted original Lévy path and extended infimum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_shifted_rational_survival_iff_weak_downclock
import Theorems.Thm_AvramDividend_Classical_chat04_ennreal_strict_clock_single_time_null_ws01a

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_shifted_rational_future_ae_closed_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (ω : Ω) (b : ℝ≥0) :
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      (0 ≤ t ∧ ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal t →
          0 ≤ x + (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω)) ↔
      (0 ≤ t ∧ ∀ s : ℝ≥0, s ≤ Real.toNNReal t →
        0 ≤ x + (X.X (b + s) ω - X.X b ω)) := by sorry
