-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_resolvent_action_without_integrability_assumptions
-- name    : AvramDividend.Classical.chat04_killed_scale_resolvent_action_without_integrability_assumptions
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:27:37.152979+00:00
-- url     : https://prove2.me/theorems/55d89a2a-f990-46ec-b0f0-78472523ff94
-- title:
--   Killed scale-function analytic resolvent acts as Wq over p with automatically verified integrability
-- statement:
--   For an unbounded-variation spectrally negative Lévy process with positive discount q and p, the analytic half-line killed resolvent density K(y)=exp(−θy)W(q+p)(x)−W(q+p)(x−y), weighted against Wq(y) over positive y, integrates exactly to Wq(x)/p. Both integrability requirements of the previously accepted conditional action theorem follow from the scale Laplace transform and compact support of the continuous causal convolution, so no extra integrability hypotheses are needed. This is purely analytic and does not assert stochastic identification of the killed resolvent.
-- source:
--   Accepted analytic action 34efb710; accepted scale shifted Laplace integrability da4289b8; positive-discount global W continuity c1b8958a and 9e68affb; newly verified causal compact integrability chat04_continuous_causal_convolution_integrable. The independent stochastic Wiener-Hopf kernel identification remains Open.

import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_density_scale_action_of_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_continuous_causal_convolution_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_scale_resolvent_action_without_integrability_assumptions
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 < q) (hp : 0 < p)
    (hθ : 0 ≤ θ) (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hzero : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ),
      Wq y * (Real.exp (-(θ * y)) * Wqp x - Wqp (x - y))) =
    Wq x / p := by sorry
