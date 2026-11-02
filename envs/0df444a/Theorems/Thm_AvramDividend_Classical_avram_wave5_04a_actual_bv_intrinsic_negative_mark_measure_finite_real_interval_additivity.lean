-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_finite_real_interval_additivity
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_finite_real_interval_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:49:09.184101+00:00
-- url     : https://prove2.me/theorems/dfee60ca-5061-4714-b19c-5eebd284f82e
-- title:
--   Almost-sure finite real additive original BV negative-mark source measure increments
-- statement:
--   For the actual bounded-variation spectrally negative Levy source, construct on a single almost-sure event a nonnegative real-valued functional J(s,t) of genuine original source negative-mark counting measure integrals. For all three ordered nonnegative times s≤t≤r, J(s,r)=J(s,t)+J(t,r) exactly, including infinite-activity jumps. Finiteness is certified by the actual-source residual domination. This is a convenient real-valued interval-increment interface for the stopped nonlinear C1 chain rule and assumes no Poisson model or complete Ito-Meyer identity.
-- source:
--   Chat04-A combines original intrinsic measure interval finiteness Proved 1e3e38bc-2a02-480f-a7f1-36e873625459 with original source negative-jump magnitude additivity Proved 6d0898c1-f766-400f-b285-00a6218064d2 and exact source measure-to-left-jump-sum identity Proved e40a85f1-31c7-4d8a-b66e-a0bd93a1554b. The proof does not import unpublished measure additivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_negative_source_jump_measure_interval_integrable_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_negative_jump_magnitude_three_endpoint_interval_additivity

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A genuine real-valued, finite, nonnegative additive increment
functional from original BV Levy left-jump negative-mark measure.
The a.s. event is uniform in all three ordered time endpoints. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_finite_real_interval_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ J : ℝ≥0 → ℝ≥0 → ℝ,
      (∀ (a b : ℝ≥0),
        J a b =
          (∫⁻ p,
            (if a < p.1 ∧ p.1 ≤ b then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal) ∧
      (∀ a b, 0 ≤ J a b) ∧
      ∀ (s t r : ℝ≥0), s ≤ t → t ≤ r →
        J s r = J s t + J t r := by sorry
