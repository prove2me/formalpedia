-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_expected_abs_bound
-- name    : AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_expected_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:16:56.101831+00:00
-- url     : https://prove2.me/theorems/fbca8160-7891-49a7-9640-7a77eb0a27af
-- title:
--   Original stopped C2 Gaussian finite mesh expected Hessian bracket absolute bound
-- statement:
--   For the original source Levy X, the stopped discounted C2 Hessian mesh with true ruin time and dividend reserve has an integrable Gaussian half-bracket drift. Assuming a uniform spatial Hessian cap K and sum of mesh durations at most T, its expected absolute Gaussian contribution is at most sigma squared K T over two. The proof uses a previous source-specific finite-mesh domination theorem and the original probability measure.
-- source:
--   Accepted original stopped C2 Hessian finite mesh total-time uniform bound, UUID c91bbceb-b4d0-4432-9900-5068bf41e3db, plus pinned Mathlib norm_integral_le_of_norm_le_const.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_total_time_uniform_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-! Original stopped Gaussian Hessian finite mesh expectation envelope. -/

theorem AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_expected_abs_bound
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
    |∫ ω, ∑ i ∈ S,
      (h i : ℝ) * (((X.σ : ℝ) ^ 2 / 2) * H i ω) ∂P| ≤
      ((X.σ : ℝ) ^ 2 / 2) * K * (T : ℝ) := by sorry
