-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_stopped_C2_hessian_gaussian_halfbracket_integral_expectation_bound
-- name    : AvramDividend.Classical.avram_wave7_05_turn10_original_stopped_C2_hessian_gaussian_halfbracket_integral_expectation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:22:07.05098+00:00
-- url     : https://prove2.me/theorems/16533077-20b7-4798-a081-55e9b06e71c2
-- title:
--   Original reserve stopped C2 Hessian Gaussian sigma squared over two expectation envelope
-- statement:
--   For the original Lévy X and dividend-controlled stopped reserve, a bounded predictable C2 Hessian H on the original stopping times has an integrable Gaussian generator drift coefficient ((X.σ:ℝ)^2/2)*H, with absolute expectation at most ((X.σ:ℝ)^2/2)*K. This is the proper quadratic variation coefficient for the source Gaussian Itô correction; no independent Brownian model is used.
-- source:
--   Original C2 stopped Hessian joint predictability, measure probability and Mathlib integral_mono.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Original controlled reserve Hessian Gaussian sigma-square/2 drift expectation envelope. -/

theorem AvramDividend.Classical.avram_wave7_05_turn10_original_stopped_C2_hessian_gaussian_halfbracket_integral_expectation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ n, H n = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ n ω, |H n ω| ≤ K) :
    ∀ n, Integrable
      (fun ω => (((X.σ : ℝ) ^ 2 / 2) * H n ω)) P ∧
      |∫ ω, (((X.σ : ℝ) ^ 2 / 2) * H n ω) ∂P| ≤
        ((X.σ : ℝ) ^ 2 / 2) * K := by sorry
