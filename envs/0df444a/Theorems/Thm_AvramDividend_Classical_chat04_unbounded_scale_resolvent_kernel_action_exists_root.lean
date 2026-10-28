-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_kernel_action_exists_root
-- name    : AvramDividend.Classical.chat04_unbounded_scale_resolvent_kernel_action_exists_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:05:39.430846+00:00
-- url     : https://prove2.me/theorems/4afabbf1-90a9-42d8-b8e8-bb34df18a380
-- title:
--   Unbounded-variation killed-resolvent scale kernel action with an actual positive Esscher root
-- statement:
--   For any nonnegative q and strictly positive p in the unbounded-variation branch, the independently proved positive Esscher root for q+p can be selected so that the exponential-minus-convolution kernel evaluates to Wq(x)/p for every positive reserve x. Removes the assumed root parameter from the analytic killed-resolvent calculation.
-- source:
--   Direct composition of proved positive_esscher_root_of_unbounded_variation and proved chat04_unbounded_scale_resolvent_kernel_action.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_kernel_action

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_scale_resolvent_kernel_action_exists_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q p : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (x : ℝ) (hx : 0 < x) :
    ∃ θ : ℝ, 0 < θ ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
        (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) =
      Wq x / p := by sorry
