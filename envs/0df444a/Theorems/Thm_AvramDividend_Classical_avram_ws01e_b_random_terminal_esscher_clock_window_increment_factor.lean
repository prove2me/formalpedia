-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_random_terminal_esscher_clock_window_increment_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_random_terminal_esscher_clock_window_increment_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:45:28.424892+00:00
-- url     : https://prove2.me/theorems/8798a683-a367-486b-a3b9-5b8fc221f27d
-- title:
--   Actual random-terminal Esscher factorisation for an adapted post-stopping increment in a clock window
-- statement:
--   Let τ≤H be a genuine stopping time of a spectrally negative Lévy process, A an event of its stopped history, and B a measurable future u-increment cylinder. Suppose this cylinder is measurable already in the filtration at L=H+1+u and C is a measurable clock window on which L≤t.toNNReal≤T. Then, under the TRUE random-observation-time Esscher density exp(θX_t−tψ(θ)) on P×ν (not a fixed-terminal substitute), the joint cylinder and clock-window probability equals Q_T(A) times the Q_u increment marginal times ν(C). The proof uses verified finite-prefix Esscher consistency at a clock, the bounded-stop future-increment law, and explicitly scoped adaptation and clock support. It does not assume a globally tilted Lévy law or Wiener–Hopf splitting.
-- source:
--   Composes canonical Proved esscher_clock_supported_stopped_event_laws_agree (51efe1af-d2be-4a72-bf21-81880a76e403) and esscher_bounded_stop_future_increment_cylinder_factor (4d8a7cfb-3725-489d-befc-72d496f9561d), plus filtration monotonicity on the actual observation-clock window.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_stopped_event_laws_agree
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_cylinder_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual random-terminal Esscher likelihood factors a bounded-stop
future-increment cylinder over a clock window lying past its adapted horizon. -/

theorem AvramDividend.Classical.avram_ws01e_b_random_terminal_esscher_clock_window_increment_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hEvent : MeasurableSet
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}))
    (hEventAdapted : MeasurableSet[𝓕 (H + 1 + u)]
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}))
    {ν : Measure ℝ} [SFinite ν]
    (C : Set ℝ) (hC : MeasurableSet C)
    (hClockLow : ∀ t ∈ C, H + 1 + u ≤ Real.toNNReal t)
    (hClockHigh : ∀ t ∈ C, Real.toNNReal t ≤ T)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) :
    ((P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ))))
      ((A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) ×ˢ C) =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B)) * ν C := by sorry
