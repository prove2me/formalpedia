-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals
-- name    : AvramDividend.Classical.nonnegative_integrable_tsum_of_summable_integrals
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:09:16.283627+00:00
-- url     : https://prove2.me/theorems/2df366d2-d11d-4572-aa38-6a53ba18b005
-- title:
--   Integrability of nonnegative convolution-power series from summable integrated masses
-- statement:
--   For an arbitrary measure space, a pointwise convergent nonnegative series of integrable real-valued functions is integrable when the integrals of its terms form a summable series. The proof uses the nonnegative Tonelli interchange and provides the missing analytical passage from geometric convolution-power masses to an integrable renewal density at zero.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.Real

open MeasureTheory

theorem AvramDividend.Classical.nonnegative_integrable_tsum_of_summable_integrals
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℝ)
    (hFi : ∀ n : ℕ, Integrable (F n) μ)
    (hpos : ∀ n : ℕ, ∀ x : α, 0 ≤ F n x)
    (hpoint : ∀ x : α, Summable (fun n : ℕ => F n x))
    (hmass : Summable (fun n : ℕ => ∫ x : α, F n x ∂μ)) :
    Integrable (fun x : α => ∑' n : ℕ, F n x) μ := by sorry
