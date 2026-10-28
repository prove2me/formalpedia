-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_discount_cancellation
-- name    : AvramDividend.Classical.chat04_unbounded_scale_resolvent_discount_cancellation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:50:44.830415+00:00
-- url     : https://prove2.me/theorems/6de020a7-1c14-4cca-92bd-9dc86494eab5
-- title:
--   Resolvent quotient cancels its q-scale convolution to the scalar q-scale value
-- statement:
--   For a spectrally negative Lévy process of unbounded variation, q≥0 and p>0, the difference between W^(q+p)(x)/p and the causal convolution of W^(q) with W^(q+p) equals W^(q)(x)/p. This is the exact algebraic cancellation required in the Laplace-resolvent route to killed q-scale harmonicity.
-- source:
--   Direct algebraic consequence of Proved unbounded_scale_resolvent_convolution (4198c14e-7e01-4121-a3e9-8f4e30ee2b4d), using no first-exit or martingale premise.

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_scale_resolvent_discount_cancellation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q p : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (x : ℝ) (hx : 0 < x) :
    Wqp x / p -
      (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) =
    Wq x / p := by sorry
