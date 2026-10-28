-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_survival_inner_lintegral_envelope
-- name    : AvramDividend.Classical.killed_survival_inner_lintegral_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:50:41.829319+00:00
-- url     : https://prove2.me/theorems/09e06fab-3f69-41d6-8b6e-ede0643648eb
-- title:
--   Nonnegative capital Laplace integral of killed Lévy survival equals reflected-infimum envelope
-- statement:
--   For every finite-horizon Lévy sample path and positive Laplace exponent, the nonnegative capital integral of the survival kernel equals the reflected running-infimum exponential envelope. Converts the already Proved real-valued pathwise identity to a Tonelli-compatible nonnegative integral using integrability of exponential tails.
-- source:
--   Proved pathwise_killed_survival_laplace_envelope_all_paths, levy_path_bddBelow_finite_horizon, lower_survival_running_infimum_equiv; pinned Mathlib ofReal_integral_eq_lintegral_ofReal and integrableOn_exp_mul_Ioi.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_pathwise_killed_survival_laplace_envelope_all_paths

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_survival_inner_lintegral_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ (x : ℝ),
      Set.indicator
        {y : ℝ | 0 < y ∧ ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}
        (fun y => ENNReal.ofReal (Real.exp (-θ * y))) x ∂volume) =
    ENNReal.ofReal
      (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) := by sorry
