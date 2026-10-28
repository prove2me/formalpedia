-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_renewal_integral_tsum_exchange
-- name    : AvramDividend.Classical.nonnegative_renewal_integral_tsum_exchange
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:32:52.396993+00:00
-- url     : https://prove2.me/theorems/c170d01a-122d-41ab-a46a-24ae25d6e310
-- title:
--   Exchange of integration and a nonnegative summable renewal-power series
-- statement:
--   A sequence of nonnegative integrable real functions whose integrated masses form a summable series satisfies interchange of the Lebesgue integral and infinite sum. For the Esscher renewal construction this is the exact real-valued Tonelli/Fubini step needed to identify the Laplace transform of the renewal density with the geometric sum of kernel transforms.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Real

open MeasureTheory

theorem AvramDividend.Classical.nonnegative_renewal_integral_tsum_exchange
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℝ)
    (hFi : ∀ n : ℕ, Integrable (F n) μ)
    (hpos : ∀ n : ℕ, ∀ x : α, 0 ≤ F n x)
    (hmass : Summable (fun n : ℕ => ∫ x : α, F n x ∂μ)) :
    (∫ x : α, ∑' n : ℕ, F n x ∂μ) =
      ∑' n : ℕ, ∫ x : α, F n x ∂μ := by sorry
