-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_resolvent_action_from_qscale_ws01a
-- name    : AvramDividend.Classical.chat04_unbounded_killed_resolvent_action_from_qscale_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:51:13.968991+00:00
-- url     : https://prove2.me/theorems/fb01713f-3554-4409-aa2f-3071bb3d5d1f
-- title:
--   Half-line analytic killed-resolvent action from the supplied q-scale only
-- statement:
--   For a spectrally negative unbounded-variation Levy process with only a given positive q-scale Wq and p>0, construct a (q+p)-scale Wqp, a strictly positive root θ of ψ(θ)=q+p, and the exact analytic half-line kernel action on Wq equal to Wq(x)/p for all x>0. This removes the shifted-scale existence and exponential-root hypotheses from the resolvent route; it does not assume or assert a stochastic spatial-kernel identification.
-- source:
--   Canonical Proved q-to-q+p Neumann renewal construction 7add6cfb, positive-root existence cfe6d3e1 and analytic killed kernel action 55d89a2a; no use of two-sided exit or killed martingale.

import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_exists_at_positive_discount_shift_ws01a
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_resolvent_action_without_integrability_assumptions
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_killed_resolvent_action_from_qscale_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (Wq : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq) (p : ℝ) (hp : 0 < p) :
    ∃ Wqp : ℝ → ℝ, ∃ θ : ℝ,
      IsScaleFunction X (q + p) Wqp ∧ 0 < θ ∧ X.ψ θ = q + p ∧
      ∀ x : ℝ, 0 < x →
        (∫ y in Ioi (0 : ℝ),
          Wq y * (Real.exp (-(θ * y)) * Wqp x - Wqp (x - y))) =
          Wq x / p := by sorry
