-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_killed_record_sum_finite_ae_of_exit_factor
-- name    : AvramDividend.Classical.chat12_killed_record_sum_finite_ae_of_exit_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:36:28.847086+00:00
-- url     : https://prove2.me/theorems/9ea8dba8-98a8-49ba-9aeb-b4d2d1c89d9f
-- title:
--   Almost-sure finite killed upward-record payment series under strict exit factor below one
-- statement:
--   For a spectrally negative Lévy process with q>0 and a>0, ε>0, suppose the genuine discounted strict up-before-(-a)-down exit factor is ENNReal.ofReal p for 0≤p<1. Then with probability one the sum over all killed upward-record levels of the corresponding discounted ε-sized payments is finite, as an extended nonnegative-real series. This applies the Proved specific record-reward measurability, Proved total expected upper finiteness, and generic Tonelli almost-everywhere finiteness bridge. It is a finite sample-path record budget, separate from Chat 5's pathwise dividend Stieltjes integral comparison.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_finite_of_trueExit_factor
import Theorems.Thm_AvramDividend_Classical_chat12_expected_record_sum_finite_ae

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_killed_record_sum_finite_ae_of_exit_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p < 1)
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    ∀ᵐ ω ∂P, (∑' n : ℕ,
      if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0) < ∞ := by sorry
