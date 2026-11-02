-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_stopped_nonlinear_downward_residual_uniform_variation_envelope
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_stopped_nonlinear_downward_residual_uniform_variation_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:25:29.688234+00:00
-- url     : https://prove2.me/theorems/397f2842-72b3-4ce9-80fb-b02c9ec6993f
-- title:
--   Uniform stopped nonlinear BV source residual loss bound by original downward variation
-- statement:
--   On a probability-one event for the actual spectrally negative bounded-variation source with its true intrinsic negative jump measure, the exact residual R is nondecreasing. Given any increasing verification function with an explicit one-sided Lipschitz slope bound M and any nonnegative weights bounded by A along a stopped monotone source partition, the total nonlinear loss from downward R increments is nonnegative and at most A*M times the true original residual variation between the partition start and stopping horizon. This provides a source-only nonlinear dominated-convergence envelope without any controlled Ito-Meyer or stochastic integral equality.
-- source:
--   Chat04-A genuine source side. Use canonical Proved exact original intrinsic source measure decomposition 09869e16-9a95-47e7-b1cd-83739a17b285; apply monotonicity, the stated explicit one-sided Lipschitz bound, scalar multiplication and exact telescoping of residual increments. It bounds all stopped finite nonlinear source losses by one BV variation budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact nonlinear source remainder increments are nonnegative losses,
and a one-sided Lipschitz bound gives a horizon-uniform BV variation
envelope, without an assumed nonlinear stochastic integral. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_stopped_nonlinear_downward_residual_uniform_variation_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : Monotone w)
    (M : ℝ) (hM : 0 ≤ M)
    (hLipDown : ∀ (y δ : ℝ), 0 ≤ δ →
      w y - w (y - δ) ≤ M * δ) :
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
        (a : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A)
        (ha : ∀ i, 0 ≤ a i ∧ a i ≤ A),
        0 ≤ (Finset.range n).sum (fun i =>
          a i * (w (riskProcess X x D (u i) ω) -
            w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))))) ∧
        (Finset.range n).sum (fun i =>
          a i * (w (riskProcess X x D (u i) ω) -
            w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))))) ≤
          (A * M) * (R (τ ω) - R (u 0)) := by sorry
