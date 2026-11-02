-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_original_controlled_hessian_stopped_gaussian_quadratic_energy_exact
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_hessian_stopped_gaussian_quadratic_energy_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:27:07.225254+00:00
-- url     : https://prove2.me/theorems/8f34e683-76c4-414e-bc2e-2e869360c36f
-- title:
--   Exact Gaussian stopped-increment quadratic energy against the genuine capped controlled reserve Hessian
-- statement:
--   For the actual SpectrallyNegativeLevy source with zero jump measure (Gaussian component), an original adapted admissible dividend control D, the exact finite-cap prepayment Hessian of a C2 test function, and an original right-continuous bounded stopping time, the expected Hessian-weighted squared centred true source increment is the expected stopped Hessian times h sigma squared. The stopped Hessian is measurable for the original stopped-history sigma algebra by its proved strong predictability. Apply the canonically proved source-path stopped Gaussian quadratic-energy factorisation. Sigma may be zero; no independent Brownian copy or equality-in-law substitution is used. This gives Chat03 a concrete second-order finite-cell Gaussian energy balance without pretending it is already continuous quadratic-variation convergence when jumps are present.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_controlled_prejump_hessian_stopped_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_quadratic_energy_exact

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_hessian_stopped_gaussian_quadratic_energy_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let H : Ω → ℝ :=
      stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      (∫ ω, H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  sorry
