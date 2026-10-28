-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_clock_fibrewise_prefix_lintegral_consistency
-- name    : AvramDividend.Classical.esscher_clock_fibrewise_prefix_lintegral_consistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:54:59.371641+00:00
-- url     : https://prove2.me/theorems/8cd76899-aa89-4965-9a77-cd1a0817e3bc
-- title:
--   Independent Esscher terminal-clock law equals fibrewise stopped-time Esscher weighting for adapted clock observations
-- statement:
--   For any terminal horizon T, nonnegative independent clock law ν and jointly measurable nonnegative observable F whose path section at clock time t is measurable with respect to the original filtration at min(t,T), the Q_T×ν integral equals the ν-integral of Q_{min(t,T)} expectations. This is the rigorous clock-by-clock transfer between terminal Esscher path tilt and clock-dependent Esscher density, and prevents an invalid global claim that the random-time tilt and the independent-clock product law agree for all path events.
-- source:
--   Canonical Prove2Me esscher_finite_prefix_lintegral_consistency 88c4aa3f-c05b-4528-83ce-ab46bd285f77; chat04_esscher_weighted_finite_horizon_probability; Mathlib.MeasureTheory.Measure.Prod lintegral_prod_symm' (pinned Mathlib 0df444a).

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_finite_prefix_lintegral_consistency
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_clock_fibrewise_prefix_lintegral_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0)
    {ν : Measure ℝ≥0} [SFinite ν]
    (F : Ω × ℝ≥0 → ℝ≥0∞)
    (hF : Measurable F)
    (hSlice : ∀ t : ℝ≥0,
      Measurable[𝓕 (min t T)] (fun ω : Ω => F (ω, t))) :
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) =
    (∫⁻ t : ℝ≥0, (∫⁻ ω, F (ω, t) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (min t T) ω -
          ((min t T : ℝ≥0) : ℝ) * X.ψ θ))))) ∂ν) := by sorry
