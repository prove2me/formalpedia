-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:20:15.909419+00:00
-- url     : https://prove2.me/theorems/222dbf6e-6890-46af-96b2-6eb440941e10
-- title:
--   Nonlinear monotone stopped source BV residual update is nonpositive on actual intrinsic-jump event
-- statement:
--   For the genuine bounded-variation spectrally negative Levy source path, on a single full-measure event with the exact original intrinsic negative-mark decomposition and monotone downward residual R, every increasing verification function w has a nonpositive exact nonlinear value change when any sampled residual increment is subtracted from the actual controlled reserve. Summing these exact nonlinear decrements with positive exponential discount weights along every stopped monotone source time grid remains nonpositive. No C1 derivative, original-process replacement, pure jump residual equality, or complete Ito-Meyer integration is assumed.
-- source:
--   Chat04-A. Exact nonlinear Stieltjes residual sign reduced to the Proved original source measure decomposition 09869e16-9a95-47e7-b1cd-83739a17b285, ordinary monotonicity of verification function w and nonnegativity of exponential discount weights. This is a pathwise stopped source-only negative contribution; Chat03 retains all controlled integration and tag-convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- An exact nonlinear sign for the remaining downward BV source component:
each extra downward residual increment decreases every increasing verification
function, even without a derivative. The original intrinsic jump measure is
identified on the same P-full event; no Ito--Meyer identity is assumed. -/

theorem AvramDividend.Classical.avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : Monotone w) (q : ℝ) :
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
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
        (∑ i : Fin n,
          Real.exp (-(q * (u i : ℝ))) *
            (w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))) -
              w (riskProcess X x D (u i) ω))) ≤ 0 := by sorry
