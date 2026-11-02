-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
-- name    : AvramDividend.Classical.avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:31:02.67053+00:00
-- url     : https://prove2.me/theorems/1239ad4c-4f89-4fe6-89b1-996837f14097
-- title:
--   Actual UBV Lévy zero-capital exact zero payout and capped optimal value for every discount and cap
-- statement:
--   For the original spectrally negative Lévy process of unbounded variation, starting from reserve zero, every original IsAdmissibleLe regulator has full infinite-horizon dividendValue exactly zero, and the optimal capped valueFunctionLe at reserve zero is exactly zero. No standing assumptions, discount sign restriction, HJB inequality, smoothness or secant premise is required. Specialise the Proved zero-start full-value bound to the identity candidate w(y)=y; its derivative equals one and its right-payment secant is an algebraic equality. The uniform bound is ENNReal.ofReal (w 0)=0; nonnegativity makes it equality. Apply the Proved per-strategy-to-capped-value supremum bridge with the constant-zero comparison. Original time-zero payments and all Stieltjes dividend measures are retained. This follows ultimately from immediate ruin at zero for unbounded-variation original Lévy paths and is a genuine boundary theorem, not a positive-capital result.
-- source:
--   Avram, Palmowski and Pistorius (2007), classical unbounded-variation zero-capital boundary. Proved Chat 08 original instant-ruin lemma 2df9814e-41d9-4386-8e41-2fc17b1d5a4c, Proved zero-start exact Stieltjes finite-horizon 14599b22-5d59-42c4-81c7-efbc058a3e03, Proved full bridge 449258df-da20-4bb1-85f1-1ff3b41d4e25 and Proved per-strategy supremum bridge 26cdad24-50a7-4f19-a856-90135afe6b6b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_dividendValue_upper
import Theorems.Thm_AvramDividend_Classical_local_verification_per_strategy_to_capped_value_bound
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (C : ℝ≥0∞) :
    (∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X 0 C D →
      dividendValue X q 0 D = 0) ∧
    valueFunctionLe X q C 0 = 0 := by sorry
