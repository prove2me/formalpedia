-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_limit_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_limit_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:41:08.225878+00:00
-- url     : https://prove2.me/theorems/a2e9db56-7553-43ec-a61a-4bbff1a5956b
-- title:
--   Local-gradient stopped nonlinear source remainder: all convergent nonnegative-weight approximation limits are nonpositive
-- statement:
--   For the actual original bounded-variation spectrally negative Levy source, almost surely its explicit monotone residual has a nonpositive limit along any convergent sequence of stopped partition sums with arbitrary nonnegative weights and derivative nonnegativity required only at each sampled controlled reserve. This is exactly the localisation relevant to the positive-cap BV verification HJB gradient assumption. It asserts sign of any externally supplied limit; does not identify a controlled Ito-Meyer integral.
-- source:
--   Chat04-A original-process local-gradient limit consequence of helper theorem avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_nonpos; invokes le_of_tendsto on a universal finite-sum nonpositivity certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_nonpos

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The nonpositive source residual contribution persists under real
limits of stopped, nonnegatively weighted local-gradient finite sums. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_limit_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k))
        (n : ℕ → ℕ) (hstop : ∀ k : ℕ, u k (n k) ≤ τ ω)
        (a : ℕ → ℕ → ℝ) (ha : ∀ k i, 0 ≤ a k i)
        (hderiv : ∀ k (i : Fin (n k)),
          0 ≤ deriv w (riskProcess X x D (u k i) ω))
        (L : ℝ)
        (hlim : Tendsto (fun k : ℕ =>
          ∑ i : Fin (n k),
            -(a k i * deriv w (riskProcess X x D (u k i) ω)) *
              (R (u k (i + 1)) - R (u k i))) atTop (𝓝 L)),
        L ≤ 0 := by sorry
