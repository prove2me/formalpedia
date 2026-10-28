-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_killed_record_sum_ae_finite_of_scale_exit
-- name    : AvramDividend.Classical.chat12_killed_record_sum_ae_finite_of_scale_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:38:09.875133+00:00
-- url     : https://prove2.me/theorems/78011857-4271-4eca-b11b-89b7414ace7c
-- title:
--   Almost-surely finite killed-record payment series under conditional q-scale exit identity
-- statement:
--   Assume the strict discounted two-sided exit factor equals W(a)/W(a+ε) for a q-scale function W whose values satisfy 0≤W(a)<W(a+ε). Then the samplewise series of discounted killed upward-record payments is finite with probability one. This combines the Proved scale-ratio finite total expectation, specific record-reward measurability, and generic Tonelli almost-everywhere finiteness theorem. The q-scale exit identity is explicitly hypothesised, not imported. This aids the Chat 5 pathwise budget without claiming the separate dividend-measure inequality.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_scale_finite_of_exit
import Theorems.Thm_AvramDividend_Classical_chat12_expected_record_sum_finite_ae

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_killed_record_sum_ae_finite_of_scale_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε))
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε))) :
    ∀ᵐ ω ∂P, (∑' n : ℕ,
      if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0) < ∞ := by sorry
