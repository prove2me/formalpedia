-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_negative_source_jump_measure_interval_integrable_finite
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_source_jump_measure_interval_integrable_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:55:28.274193+00:00
-- url     : https://prove2.me/theorems/1e3e38bc-2a02-480f-a7f1-36e873625459
-- title:
--   Actual BV source intrinsic negative left-jump integral is finite on every ordered time interval almost surely
-- statement:
--   For the actual bounded-variation spectrally negative Levy source, almost surely its intrinsic original-path negative left-jump measure has a finite negative-mark magnitude integral over every ordered time interval (s,t]. This follows directly from the already Proved upper domination by the finite actual source drift residual. The theorem uses the intrinsic original sample-path counting measure rather than a Poisson model or an assumed pure-jump equality. It establishes finite mass of the relevant weighted jump mark integrand, not finite total count of jump times.
-- source:
--   Chat04-A directly derives intrinsic source negative-mark interval finiteness from canonically Proved actual source jump-integral residual domination cbc2e9a0-6ab9-4203-bcc0-c4a96882d592; no independent Poisson process or Lévy-Ito path equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_intrinsic_negative_jump_integral_le_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On almost every actual original BV Levy path, the intrinsic source
negative left-jump magnitude integral is finite on every compact
time interval. This is a corollary of the genuine residual domination. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_source_jump_measure_interval_integrable_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (∫⁻ p,
        (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≠ ⊤ := by sorry
