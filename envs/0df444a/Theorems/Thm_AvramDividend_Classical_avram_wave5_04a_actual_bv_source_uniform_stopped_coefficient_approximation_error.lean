-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_uniform_stopped_coefficient_approximation_error
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_uniform_stopped_coefficient_approximation_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:14:33.485537+00:00
-- url     : https://prove2.me/theorems/d99f6bce-8647-4368-9e42-cff57aa05253
-- title:
--   Actual original BV source: uniform stopped-horizon error bound for sampled nonlinear C1 coefficient approximation
-- statement:
--   For the actual spectrally negative Levy source of bounded variation, almost surely the explicitly defined original-source monotone residual has the following property: along every samplewise stopped ordered time partition, the difference of two residual finite-variation weighted sums is uniformly bounded by the maximum coefficient error M times the total residual increment up to the stopping horizon. This is a mesh-independent nonlinear C1 coefficient-approximation estimate and assumes no pure-jump equality or controlled Ito-Meyer chain rule.
-- source:
--   Chat04-A source-only stopped C1 uniform approximation: follows from canonically Proved original source coefficient Lipschitz estimate 04aefb9c-3519-47c6-b349-52bd61154dc3 and monotonicity of its unique actual source BV remainder.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_stopped_weighted_sum_lipschitz_stability

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A source-only, horizon-uniform C1 coefficient-approximation error
estimate for the genuine original BV source residual. No stochastic
integration identity is assumed, and R is the actual source residual. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_uniform_stopped_coefficient_approximation_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (a b : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (hab : ∀ i : ℕ, |a i - b i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i))) -
          (Finset.range n).sum (fun i =>
            b i * (R (u (i + 1)) - R (u i)))| ≤
          M * (R (τ ω) - R (u 0)) := by sorry
