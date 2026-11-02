-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_one_remainder_exact_source_increment_and_local_gradient_weighted_sign
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_one_remainder_exact_source_increment_and_local_gradient_weighted_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:53:57.857911+00:00
-- url     : https://prove2.me/theorems/a12b5887-5cf8-4303-80d1-2ec856518ab4
-- title:
--   One original BV source residual: exact left-jump increment decomposition and local-gradient weighted stopped sign
-- statement:
--   For the actual original bounded-variation spectrally negative Levy process, on a single probability-one event one uniquely defined residual R simultaneously gives exact drift-minus-complete-intrinsic-left-jump-minus-R interval increments and nonpositive weighted stopped derivative sums under derivative nonnegativity only at sampled positive-cap controlled reserves. This interface does not assume global monotonicity of the final HJB supersolution, a pure-jump equality or controlled Ito-Meyer integration.
-- source:
--   Chat04-A direct interface for Chat03 and Chat04; combines independently Proved exact original-source increment c4b53c7c-d769-4894-a0d8-c0b2a1516d1e with local-gradient weighted residual theorem b623ab75-62e9-4ee8-862e-c7ede382a174, identifying the source residual witnesses via explicit formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_nonpos

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A single actual BV source residual has exact intrinsic left-jump
increments and a nonpositive weighted C1 contribution under sampled
local derivative conditions, sufficient for positive-cap localisation. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_one_remainder_exact_source_increment_and_local_gradient_weighted_sign
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
      (∀ (s t : ℝ≥0) (hst : s ≤ t),
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∑' (v : ℝ≥0),
              if s < v ∧ v ≤ t then
                ENNReal.ofReal (Function.leftLim
                  (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
              else 0).toReal -
            (R t - R s)) ∧
      (∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
        (hderiv : ∀ i : Fin n,
          0 ≤ deriv w (riskProcess X x D (u i) ω)),
        (∑ i : Fin n,
          -(a i * deriv w (riskProcess X x D (u i) ω)) *
            (R (u (i + 1)) - R (u i))) ≤ 0) := by sorry
