-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_controlled_gaussian_finite_C2_mesh_expected_half_bracket
-- name    : AvramDividend.Classical.avram_wave7_05_turn3_original_controlled_gaussian_finite_C2_mesh_expected_half_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:13:12.483795+00:00
-- url     : https://prove2.me/theorems/51ce523d-26b0-473b-8f4c-77c101788c7e
-- title:
--   Finite actual-process controlled C2 Gaussian Taylor mesh has expected sigma-square half-bracket
-- statement:
--   For a finite family of genuine bounded source stopping times on the original Ω, filtration and SpectrallyNegativeLevy process, and one true dividend strategy D, the discounted, ruin-killed controlled predividend gradient times a source centred Gaussian stopped increment plus one half of the controlled Hessian times its square is integrable, including the entire finite sum. Its expected sum is exactly the sum over stopped cells of h_i σ²/2 times the same original stopped Hessian. This gives the finite stopped C² Gaussian half-bracket component with correct coefficient and integrability, under ν=0 and explicit bounded localisation. This is a finite mesh, not yet a continuous-time limit and not the nonzero-jump source Ito theorem.
-- source:
--   Specialises Proved original Wave6 controlled C2 Gaussian total conditional expectation lemma 6242d57f-1e88-4cec-8f52-6ddc12acf9d0 and Wave7 expected Taylor cell 503d9be1-caac-4af3-9e40-45c703b3c635; adds finite stopped family integrability and exact sum of expected half-bracket terms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_total_condExp_cell
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_discounted_ruin_controlled_gaussian_expected_taylor_cell

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn3_original_controlled_gaussian_finite_C2_mesh_expected_half_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B)
    (h : ι → ℝ≥0)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hGbound : ∀ i ∈ S, ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) ω| ≤ K₁)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hHbound : ∀ i ∈ S, ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) ω| ≤ K₂) :
    let G : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let H : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let Y : ι → Ω → ℝ := fun i ω =>
      X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
    (∀ i ∈ S, Integrable (fun ω =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2) P) ∧
    Integrable (fun ω => Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2)) P ∧
    (∫ ω, Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2) ∂P) =
      ∑ i ∈ S, (∫ ω,
        ((h i : ℝ) * X.σ ^ 2 / 2) * H i ω ∂P) := by sorry
