-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_aelimit_integrals
-- name    : AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_aelimit_integrals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:11:06.700207+00:00
-- url     : https://prove2.me/theorems/71359fee-f671-4692-a66c-48d2c18c5a72
-- title:
--   Original Gaussian C2 Hessian finite mesh expectation convergence under total-time bound
-- statement:
--   For the original Levy source X, original filtration, ruin stopping and dividend-reserve Hessian, finite Gaussian halfbracket mesh sums with deterministic total duration at most T and bounded stopped C2 Hessian K admit an integrable constant domination independent of mesh count. Any almost-everywhere pointwise limit of these mesh sums has convergence of their Bochner expectations. The existence and identification of the full Ito Hessian integral remain separate hypotheses.
-- source:
--   Direct use of Proved original stopped Gaussian finite mesh uniform bracket bound (turn11) with Mathlib Bochner dominated convergence.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_total_time_uniform_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-! Original stopped Gaussian Hessian drift passage along a finite mesh. -/

theorem AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_aelimit_integrals
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
    Tendsto (fun n => ∫ ω, ∑ i ∈ S n,
      (h n i : ℝ) * (((X.σ : ℝ) ^ 2 / 2) * H n i ω) ∂P)
      atTop (nhds (∫ ω, L ω ∂P)) := by sorry
