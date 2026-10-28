-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_unbounded_clock_tail_increment_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_support_unbounded_clock_tail_increment_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T07:54:56.965116+00:00
-- url     : https://prove2.me/theorems/950c9d14-79ce-4cc1-b11e-5034b1735ee0
-- title:
--   Unbounded exponential-clock tail Esscher stopped-increment factorisation
-- statement:
--   For a bounded genuine Lévy stopping time and stopped-history event A, a future u-increment Borel cylinder measurable at s=H+1+u, and any measurable C of independent exponential-clock ages t with t.toNNReal≥s, the genuine random-terminal Esscher mass of the stopped cylinder times C equals Q_s(A) times the genuine Esscher increment marginal Q_u(B) times Exp(p)(C). Unlike the existing bounded-clock-window factor, no upper bound on the clock is assumed. This uses exact past-clock factorisation at s and the accepted bounded stopped-increment cylinder, without assuming global tilted path independence.
-- source:
--   Canonical accepted esscher_random_time_joint_past_clock_future_factorization (caa0f80f-72fe-4f00-ad06-c2fe43ac38d4) and esscher_bounded_stop_future_increment_cylinder_factor (4d8a7cfb-3725-489d-befc-72d496f9561d).

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_esscher_random_time_joint_past_clock_future_factorization
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_cylinder_factor
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Genuine random-time Esscher stopped-increment factorisation on an
unbounded upper tail of the independent exponential clock. -/

theorem AvramDividend.Classical.avram_ws01e_b_support_unbounded_clock_tail_increment_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u : ℝ≥0)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hEventAdapted : MeasurableSet[𝓕 (H + 1 + u)]
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}))
    (C : Set ℝ) (hC : MeasurableSet C)
    (hClockLow : ∀ t ∈ C, H + 1 + u ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ))))
      ((A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) ×ˢ C) =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (H + 1 + u) ω -
        ((H + 1 + u : ℝ≥0) : ℝ) * X.ψ θ)))) A *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B)) * (expMeasure p) C := by sorry
