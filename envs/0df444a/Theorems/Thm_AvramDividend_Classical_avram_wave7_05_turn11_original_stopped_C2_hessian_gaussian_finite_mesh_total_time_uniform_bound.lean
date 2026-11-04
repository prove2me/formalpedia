-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_total_time_uniform_bound
-- name    : AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_total_time_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:07:26.304572+00:00
-- url     : https://prove2.me/theorems/c91bbceb-b4d0-4432-9900-5068bf41e3db
-- title:
--   Original stopped C2 Gaussian Hessian total-time finite mesh bracket bound
-- statement:
--   For the actual canonical spectrally negative Levy X on its original probability space and filtration and a genuine dividend strategy D, every finite collection of stopped discounted C2 Hessians bounded by K has an integrable Gaussian variance drift sum with exact sigma squared over two. If the total mesh duration is at most T, that sum is pathwise bounded in absolute value by sigma squared K T over two. This uniform bound is independent of mesh cardinality and supports a dominated-convergence passage in the Gaussian Ito drift.
-- source:
--   Original stopped Hessian Gaussian halfbracket expectation bound, UUID 16533077-20b7-4798-a081-55e9b06e71c2, and pinned Mathlib Finset absolute sum inequality.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_stopped_C2_hessian_gaussian_halfbracket_integral_expectation_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-! Original stopped C2 Hessian Gaussian bracket mesh domination. -/

theorem AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_total_time_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0) (S : Finset ℕ)
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
    (hHbound : ∀ n ω, |H n ω| ≤ K)
    (h : ℕ → ℝ≥0)
    (hTotal : (∑ i ∈ S, (h i : ℝ)) ≤ (T : ℝ)) :
    Integrable (fun ω => ∑ i ∈ S,
      (h i : ℝ) * (((X.σ : ℝ) ^ 2 / 2) * H i ω)) P ∧
    ∀ ω, |∑ i ∈ S,
      (h i : ℝ) * (((X.σ : ℝ) ^ 2 / 2) * H i ω)| ≤
      ((X.σ : ℝ) ^ 2 / 2) * K * (T : ℝ) := by sorry
