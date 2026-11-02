-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_source_measure_and_discounted_stopped_C1_real_limit_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_source_measure_and_discounted_stopped_C1_real_limit_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:47:31.797612+00:00
-- url     : https://prove2.me/theorems/1cf98b31-7127-4034-8471-7f5dfa8181bc
-- title:
--   One actual BV source event for exact intrinsic jump-measure decomposition and nonpositive convergent stopped C1 remainder
-- statement:
--   For an actual bounded-variation spectrally negative Levy source X, an actual dividend strategy D and a verification function with the positive-cap local HJB derivative condition, one probability-one event simultaneously gives a canonical monotone original source residual, the exact source drift minus genuine intrinsic negative-mark integral minus residual source interval decomposition, and nonpositive limits of any independently supplied convergent sequence of stopped discounted residual C1 partition sums whose sampled reserve values remain in (0,C). No pure-jump equality, stochastic integration identity, convergence theorem or independent Poisson process is assumed.
-- source:
--   Chat04-A derives the exact original BV intrinsic-measure source interval identity directly from two canonically Proved actual-path results c4b53c7c-d769-4894-a0d8-c0b2a1516d1e and e40a85f1-31c7-4d8a-b66e-a0bd93a1554b, and combines it with Proved positive-cap discounted C1 stopped residual real-limit sign a2edb8c9-c132-4f57-b238-e2c21674d0b3. Residual witnesses agree pointwise by explicit formulas; no dependency on the queued exact-measure bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_positive_cap_HJB_stopped_limit_nonpos

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Single original BV source sample event for the true intrinsic
negative-mark measure decomposition and the nonpositive limit of
any convergent stopped discounted C1 residual partition sums. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_source_measure_and_discounted_stopped_C1_real_limit_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      (∀ (s t : ℝ≥0), s ≤ t →
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∫⁻ p,
              (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
              ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim
                    (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
            (R t - R s)) ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k))
        (n : ℕ → ℕ) (hstop : ∀ k : ℕ, u k (n k) ≤ τ ω)
        (hinterior : ∀ k (i : Fin (n k)),
          0 < riskProcess X x D (u k i) ω ∧
            ENNReal.ofReal (riskProcess X x D (u k i) ω) < C)
        (L : ℝ)
        (hlim : Tendsto (fun k : ℕ =>
          ∑ i : Fin (n k),
            -(Real.exp (-(q * (u k i : ℝ))) *
              deriv w (riskProcess X x D (u k i) ω)) *
                (R (u k (i + 1)) - R (u k i))) atTop (𝓝 L)),
        L ≤ 0 := by sorry
