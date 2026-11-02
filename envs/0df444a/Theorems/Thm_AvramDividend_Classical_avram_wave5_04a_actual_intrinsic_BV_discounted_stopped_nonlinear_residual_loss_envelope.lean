-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_discounted_stopped_nonlinear_residual_loss_envelope
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_discounted_stopped_nonlinear_residual_loss_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:42:28.14645+00:00
-- url     : https://prove2.me/theorems/1e7c2f83-7274-4996-ae45-2a80c1988e08
-- title:
--   Actual BV source stopped discounted nonlinear residual loss dominated by source downward variation
-- statement:
--   On one probability-one event for the actual spectrally negative bounded variation source, the explicitly identified nondecreasing original jump-free downward residual R causes a discounted nonlinear stopped-grid correction whose loss is between zero and M times the actual R variation up to the stopping horizon. Discount weights are the physical e^(-q t) for q≥0 and need no artificial source or stochastic integral equality. For a C1 verification function, the explicit one-sided Lipschitz premise can be obtained from a local derivative upper bound by an ordinary deterministic mean-value argument in Chat03.
-- source:
--   Chat04-A original-source corollary of canonical Proved stopped nonlinear uniform BV variation theorem 397f2842-72b3-4ce9-80fb-b02c9ec6993f, with actual physical discount weights exp(-q*t) between zero and one. No C1 chain rule is assumed and no time-zero or chronological right dividends are mislabelled as original jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_stopped_nonlinear_downward_residual_uniform_variation_envelope

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Discounted original-source nonlinear downward residual loss is nonnegative and dominated by stopped source variation, without Ito-Meyer. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_discounted_stopped_nonlinear_residual_loss_envelope
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
      ∀ (q : ℝ) (hq : 0 ≤ q)
        (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
        0 ≤ (Finset.range n).sum (fun i =>
          Real.exp (-q * (u i : ℝ)) *
            (w (riskProcess X x D (u i) ω) -
              w (riskProcess X x D (u i) ω -
                (R (u (i + 1)) - R (u i))))) ∧
        (Finset.range n).sum (fun i =>
          Real.exp (-q * (u i : ℝ)) *
            (w (riskProcess X x D (u i) ω) -
              w (riskProcess X x D (u i) ω -
                (R (u (i + 1)) - R (u i))))) ≤
          M * (R (τ ω) - R (u 0)) := by sorry
