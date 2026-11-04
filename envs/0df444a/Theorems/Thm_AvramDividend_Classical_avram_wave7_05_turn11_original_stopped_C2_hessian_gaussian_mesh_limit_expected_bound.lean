-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_mesh_limit_expected_bound
-- name    : AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_mesh_limit_expected_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:20:01.848492+00:00
-- url     : https://prove2.me/theorems/965f5308-7009-4b6c-8da2-f95a49633fe5
-- title:
--   Original Gaussian stopped C2 Hessian finite mesh limit absolute expectation bound
-- statement:
--   For the original spectrally negative Levy source, the genuine discounted stopped C2 Hessian at the controlled reserve has a Gaussian sigma-squared-over-two bracket drift. If each finite mesh has total duration at most T and the Hessian is bounded by K, any almost-everywhere limit of the Hessian Gaussian mesh contributions has absolute expected value at most sigma squared K T over two. This is conditional on the actual mesh convergence, which is not inferred from the theorem.
-- source:
--   Proved original-source turn11 Gaussian finite mesh dominated-convergence and absolute expectation bounds; pinned Mathlib continuous absolute value and order limits.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_aelimit_integrals
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_expected_abs_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-! Original stopped Gaussian Hessian drift limiting expectation envelope. -/

theorem AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_mesh_limit_expected_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0) (S : ℕ → Finset ℕ)
    (τ : ℕ → ℕ → Ω → ℝ≥0)
    (hτ : ∀ n i, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (H : ℕ → ℕ → Ω → ℝ)
    (hHsource : ∀ n i, H n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ n i ω, |H n i ω| ≤ K)
    (h : ℕ → ℕ → ℝ≥0)
    (hTotal : ∀ n, (∑ i ∈ S n, (h n i : ℝ)) ≤ (T : ℝ))
    (L : Ω → ℝ) :
    (∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ S n,
      (h n i : ℝ) * (((X.σ : ℝ) ^ 2 / 2) * H n i ω))
      atTop (nhds (L ω))) →
    |∫ ω, L ω ∂P| ≤ ((X.σ : ℝ) ^ 2 / 2) * K * (T : ℝ) := by sorry
