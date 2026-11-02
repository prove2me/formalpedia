-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_measure_decomposition_and_discounted_stopped_C1_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_measure_decomposition_and_discounted_stopped_C1_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:46:57.321607+00:00
-- url     : https://prove2.me/theorems/5e0ddd91-2fd1-4987-90a7-4cfbd392ea21
-- title:
--   One a.s. event for exact intrinsic BV source measure decomposition and nonpositive discounted stopped C1 remainder
-- statement:
--   For the true bounded-variation spectrally negative Levy source and a genuine dividend strategy, the same almost-sure explicitly defined monotone residual R simultaneously satisfies the exact source increment formula in terms of the original intrinsic negative-mark measure, and gives a nonpositive discounted stopped C1 source contribution whenever sampled controlled reserves remain strictly inside the positive cap HJB derivative strip. This is a direct original-process nonlinear-chain-rule interface independent of Chat03's controlled Ito-Meyer theorem; it does not assert the residual vanishes, and source left jumps remain distinct from chronological right dividends.
-- source:
--   Chat04-A joint source-measure/C1 contribution interface deriving the exact intrinsic measure formula directly from two canonically Proved actual-source identities c4b53c7c-d769-4894-a0d8-c0b2a1516d1e and e40a85f1-31c7-4d8a-b66e-a0bd93a1554b, then combining the canonically Proved positive-cap stopped HJB gradient source residual sign 8f5999b2-9e94-4eb9-bdde-9b59ac11acbf. All residual witnesses coincide by explicit definition. No dependency on the separately queued exact measure theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One almost-sure original BV source residual simultaneously gives
the exact physical intrinsic measure decomposition and the nonpositive
discounted stopped C1 contribution on the positive-cap HJB interior. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_measure_decomposition_and_discounted_stopped_C1_nonpos
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
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hinterior : ∀ i : Fin n,
          0 < riskProcess X x D (u i) ω ∧
            ENNReal.ofReal (riskProcess X x D (u i) ω) < C),
        (∑ i : Fin n,
          -(Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)) *
              (R (u (i + 1)) - R (u i))) ≤ 0 := by sorry
