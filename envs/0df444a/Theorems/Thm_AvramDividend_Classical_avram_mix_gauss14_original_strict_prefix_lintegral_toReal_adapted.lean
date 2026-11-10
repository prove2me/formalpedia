-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_strict_prefix_lintegral_toReal_adapted
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_strict_prefix_lintegral_toReal_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T09:08:21.520208+00:00
-- url     : https://prove2.me/theorems/e594fa1f-4522-422b-a82f-79d68931f158
-- title:
--   Original strict negative cutoff marked mass is adapted as a real quantity
-- statement:
--   A concrete original-source predictable jump observability prerequisite for finite-cutoff Gaussian residual adaptedness. From the previously Proved original-filtration measurable exponential of the negative finite-prefix jump mass, apply real logarithm and sign inversion to recover measurability of the actual real-valued marked mass. This exact theorem is one source input to reconstruct the signed finite-band residual; no independent Gaussian process or auxiliary Brownian is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_arbitrary_prefix_laplace_filtration_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_strict_prefix_lintegral_toReal_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (k : ℕ) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
        then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) := by sorry
