-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_halfline_scale_resolvent_kernel_action_exists_root
-- name    : AvramDividend.Classical.chat04_unbounded_halfline_scale_resolvent_kernel_action_exists_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:42:07.072296+00:00
-- url     : https://prove2.me/theorems/bbbb9695-f1f7-470a-b7a9-dd59b8e32790
-- title:
--   Root-free existence of the full-half-line killed scale resolvent kernel action
-- statement:
--   For every nonnegative discount q, strictly positive resolvent increment p and positive reserve x, there is a positive exponential parameter delivering the exact full-half-line scale resolvent kernel action. Compose the existing proved root-existence kernel identity with scale support restriction.
-- source:
--   Direct combination of the Proved kernel-action-with-root-existence theorem and Proved convolution support restriction theorem.

import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_kernel_action_exists_root
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_convolution_support_restrict

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_halfline_scale_resolvent_kernel_action_exists_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hzero : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 < x) :
    ∃ θ : ℝ, 0 < θ ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
        (∫ y in Ioi (0 : ℝ), Wq y * Wqp (x - y)) =
      Wq x / p := by sorry
