-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_nested_C2_clock_and_preexit_discounted_energy
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_nested_C2_clock_and_preexit_discounted_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:40:55.411521+00:00
-- url     : https://prove2.me/theorems/70e79e07-db49-4434-ad3c-0a12487a910e
-- title:
--   One original nested stopping-clock family with pre-supremum C2 discounted energy
-- statement:
--   The actual nested original post-payment reserve dense-grid exit clocks are right-continuous-filtration stopping times, monotone and strictly cover their supremum. For the same clocks any finite time below the supremum has a finite stage controlling the source-exact discounted value, gradient and second-derivative Lebesgue integrals.
-- source:
--   Non-circular conjunction of two Proved original-source Wave-7 inputs 9073b48f and 1bad97a6, on definitionally identical finite-stage clocks. Does not assume or claim exhaustion of natural ruin/horizon time, stochastic mean-zero or Gaussian Ito budget.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_original_nested_C2_clock_and_preexit_discounted_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (lower upper : ℕ → ℝ) (B : ℕ → ℝ≥0)
    (hlower : ∀ n, 0 < lower n)
    (hband : ∀ n, lower n ≤ upper n)
    (hlo : ∀ n, lower (n + 1) ≤ lower n)
    (hup : ∀ n, upper n ≤ upper (n + 1))
    (hcap : ∀ n, ∀ y ∈ Set.Icc (lower n) (upper n), ENNReal.ofReal y < C)
    (hB : ∀ n, B n ≤ B (n + 1)) :
    let τ : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)
    let τSup : Ω → WithTop ℝ≥0 := fun ω => ⨆ n, τ n ω
    (∀ n, IsStoppingTime 𝓕.rightCont (τ n)) ∧
      (∀ n ω, τ n ω ≤ τ (n + 1) ω) ∧
      (∀ ω (t : WithTop ℝ≥0), t < τSup ω ↔ ∃ n, t < τ n ω) ∧
      ∀ (ω : Ω) (T : ℝ≥0), (T : WithTop ℝ≥0) < τSup ω →
        ∃ (n : ℕ) (M : ℝ), 0 ≤ M ∧
          (T : WithTop ℝ≥0) ≤ τ n ω ∧
          ∀ (A : Set ℝ), MeasurableSet A →
            (volume : Measure ℝ) A < ⊤ →
            (∀ t ∈ A, 0 ≤ t ∧ t.toNNReal < T) →
            let E : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal
              (|Real.exp (-(q * (t.toNNReal : ℝ))) *
                  w (riskProcess X x D t.toNNReal ω)| +
                |Real.exp (-(q * (t.toNNReal : ℝ))) *
                  deriv w (riskProcess X x D t.toNNReal ω)| +
                |Real.exp (-(q * (t.toNNReal : ℝ))) *
                  deriv (deriv w) (riskProcess X x D t.toNNReal ω)|)
            (∫⁻ t : ℝ, A.indicator E t ∂(volume : Measure ℝ)) < ⊤:= by sorry
