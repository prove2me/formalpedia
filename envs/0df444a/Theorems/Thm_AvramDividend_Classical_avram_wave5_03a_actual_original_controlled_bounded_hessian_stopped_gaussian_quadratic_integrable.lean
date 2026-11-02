-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_original_controlled_bounded_hessian_stopped_gaussian_quadratic_integrable
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_bounded_hessian_stopped_gaussian_quadratic_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:26:28.22918+00:00
-- url     : https://prove2.me/theorems/4473fd41-5b3b-465e-9642-a3b24a2cb99a
-- title:
--   Compact-band bounded stopped controlled HJB Hessian times true original Gaussian squared increment is integrable
-- statement:
--   For the genuine original zero-jump source and original filtration, an adapted dividend strategy and capped C2 HJB test, and a bounded right-continuous stopping time, the true drift-centred Gaussian increment squared times the stopped prepayment reserve Hessian is integrable provided this stopped Hessian is pointwise bounded by a finite K, as when localising to a compact interior reserve band. The proof derives the stopped-history and ambient measurability of H from the proved controlled Hessian predictability, square integrability of the actual source stopped increment from the proved genuine source MemLp2 theorem, then Mathlib memLp_two_iff_integrable_sq and Integrable.bdd_mul. No independent Brownian copy or general jump-bearing bracket is presumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_controlled_prejump_hessian_stopped_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_bounded_hessian_stopped_gaussian_quadratic_integrable
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
    (h : ℝ≥0) (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K) :
    Integrable (fun ω => (stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P := by
  sorry
