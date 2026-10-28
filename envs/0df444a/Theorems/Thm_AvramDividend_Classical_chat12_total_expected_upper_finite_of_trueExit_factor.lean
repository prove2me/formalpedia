-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_finite_of_trueExit_factor
-- name    : AvramDividend.Classical.chat12_total_expected_upper_finite_of_trueExit_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:58:48.543919+00:00
-- url     : https://prove2.me/theorems/c3b9c5d6-ddae-4998-ab56-5c4e77cc70fb
-- title:
--   Finiteness of total discounted expected killed-record rewards when strict exit factor is less than one
-- statement:
--   For q>0, ε>0 and a>0, suppose the true discounted strict ε-up-before-(-a)-down exit expectation equals ENNReal.ofReal p with 0≤p<1. Then the sum over all n≥0 of the expected discounted killed nε upward-record rewards is finite in ENNReal. The result follows from the Proved closed-form upper expected-record geometric bound and the Proved algebraic finiteness of ε/(1-p). No still-Open q-scale identity or pathwise dividend-measure estimate is used.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_geometric_closed_form
import Theorems.Thm_AvramDividend_Classical_chat12_geometric_budget_lt_top_of_ratio_lt_one

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_total_expected_upper_finite_of_trueExit_factor
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
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) < ∞ := by sorry
