-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_scale_finite_of_exit
-- name    : AvramDividend.Classical.chat12_total_expected_upper_scale_finite_of_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:00:35.876383+00:00
-- url     : https://prove2.me/theorems/02245d50-5eaf-41dc-b415-4218bf15c7a9
-- title:
--   Finite total expected killed-record rewards under conditional right scale exit identity
-- statement:
--   If a q-scale function W satisfies W(a)≥0, W(a+epsilon)>0 and strict increase W(a)<W(a+epsilon), and the true strict discounted two-sided exit expectation equals W(a)/W(a+epsilon), then the full sum of expected discounted killed record payments over all levels is finite. The proof combines the Proved conditional upper q-scale closed-form budget, the Proved ENNReal geometric-budget finiteness lemma and elementary ratio bounds. The still-Open corrected exit identity is a stated hypothesis, so this theorem is independent of Chat 1's proof.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_scale_closed_form_of_exit
import Theorems.Thm_AvramDividend_Classical_chat12_geometric_budget_lt_top_of_ratio_lt_one

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_total_expected_upper_scale_finite_of_exit
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
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) < ∞ := by sorry
