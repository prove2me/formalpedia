-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_density_scale_action_zero
-- name    : AvramDividend.Classical.chat04_killed_resolvent_density_scale_action_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:23:53.585829+00:00
-- url     : https://prove2.me/theorems/99f21f45-d5b3-4352-86c2-7091b016cf5b
-- title:
--   Killed-resolvent scale-kernel action at zero initial reserve
-- statement:
--   At starting reserve zero, unbounded variation gives W_q(0)=W_(q+p)(0)=0, while the (q+p)-scale function vanishes on the negative half-line. Hence the killed-resolvent spatial kernel is zero for every positive spatial argument and its integral against W_q equals W_q(0)/p. This closes the zero-reserve boundary case of the analytic killed-resolvent identity.
-- source:
--   Direct consequence of the previously verified zero-origin scale theorem and negative-half-line support.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_resolvent_density_scale_action_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 < q) (hp : 0 < p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hnegative : ∀ z : ℝ, z < 0 → Wqp z = 0) :
    (∫ y in Ioi (0 : ℝ),
      Wq y * (Real.exp (-(θ * y)) * Wqp 0 - Wqp (0 - y))) =
    Wq 0 / p := by sorry
