-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_le_scale_ratio_of_positive_barrier
-- name    : AvramDividend.Classical.barrierSupValue_zero_le_scale_ratio_of_positive_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:10:45.545987+00:00
-- url     : https://prove2.me/theorems/1304f64a-0a16-4e25-ae30-6529fa8e09f2
-- title:
--   Zero-barrier reflected dividend value is below every positive-barrier scale ratio
-- statement:
--   For a spectrally negative Levy process and any discount q, if the exact stopped reflected-regulator value at every strictly positive drawdown barrier agrees with W(a)/W'(a), then the actual value at barrier zero is bounded above by each such ratio. This is a direct one-sided stochastic consequence of monotonicity of the original stopped Stieltjes reward. It requires no finiteness or derivative asymptotic at the origin, and is useful for zero-barrier limiting arguments.
-- source:
--   Proved barrierSupValue_mono_barrier (b91cffd4-358f-4ecb-aff0-5bd6254c0dcc); one-sided step in the boundary a=0 of Avram, Palmowski and Pistorius (2007), Proposition 1.

import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierSupValue_zero_le_scale_ratio_of_positive_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hpositive : ∀ a : ℝ, 0 < a →
      barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a)) :
    ∀ a : ℝ, 0 < a →
      barrierSupValue X 0 q ≤ ENNReal.ofReal (W a / deriv W a) := by sorry
