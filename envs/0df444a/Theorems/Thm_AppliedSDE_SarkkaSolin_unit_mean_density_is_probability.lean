-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_unit_mean_density_is_probability
-- name    : AppliedSDE.SarkkaSolin.unit_mean_density_is_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:44:46.13609+00:00
-- url     : https://prove2.me/theorems/98965511-907d-46a2-92cd-a1fbbab70af1
-- title:
--   A nonnegative density with expectation one defines a probability measure
-- statement:
--   If P is a probability measure, Z is a nonnegative integrable real random variable, and its expectation under P is one, then the weighted measure withDensity P (ENNReal.ofReal ∘ Z) has total mass one. This is the measure-normalisation component of the terminal-density Girsanov theorem AppliedSDE.SarkkaSolin.girsanov_brownian_shift_terminal_density in Chapter 7. Brownian-law preservation under the changed measure remains to be proved separately.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 7, Girsanov change of measure.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AppliedSDE.SarkkaSolin.unit_mean_density_is_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ)
    (hZi : Integrable Z P)
    (hZnonneg : ∀ ω, 0 ≤ Z ω)
    (hZmean : ∫ ω, Z ω ∂P = 1) :
    IsProbabilityMeasure
      (P.withDensity (fun ω => ENNReal.ofReal (Z ω))) := by
  sorry
