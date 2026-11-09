-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_sameX_gaussian_stopped_mesh_L1_center
-- name    : AvramDividend.Classical.avram_ubv_top12_original_zero_nu_sameX_gaussian_stopped_mesh_L1_center
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:23:53.972461+00:00
-- url     : https://prove2.me/theorems/110dda8d-e87b-47fb-a55b-e4e11620e7aa
-- title:
--   Actual zero-jump original-process stopped Gaussian mesh L1-limit is centred
-- statement:
--   Under zero source jump intensity, the actual compensated original Lévy increments, with predictable stopped gradient and Hessian coefficients, have a centred L1 mesh limit. The Gaussian component uses exactly the original X on the original probability space and right-continuous filtration; no auxiliary Gaussian process or independence assumption is introduced.
-- source:
--   Specialises Proved 6de09ea4 original predictable stopped Gaussian L1 centring with its Gaussian process Y set to the unchanged X and both jump components identically zero. The source-decomposition assumption is an elementary same-X algebraic identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_top12_original_zero_nu_sameX_gaussian_stopped_mesh_L1_center
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hbounded : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hGstopped : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i) (hτ n i hi)).measurableSpace]
        (G n i))
    (hHstopped : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i) (hτ n i hi)).measurableSpace]
        (H n i))
    (hGglobal : ∀ n, ∀ i ∈ S n, Measurable (G n i))
    (hHglobal : ∀ n, ∀ i ∈ S n, Measurable (H n i))
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : ∀ u ω, Z u ω = X.X u ω - (u : ℝ) * X.c)
    (hGI : ∀ n, ∀ i ∈ S n, Integrable (fun ω => G n i ω *
      (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω)) P)
    (hHI : ∀ n, ∀ i ∈ S n, Integrable (H n i) P)
    (hH2I : ∀ n, ∀ i ∈ S n, Integrable (fun ω => H n i ω *
      (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) ^ 2) P)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f P)
    (F : ℕ → Ω → ℝ)
    (hF : ∀ n ω, F n ω = ∑ i ∈ S n,
        (G n i ω * (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) +
        (1 / 2 : ℝ) * H n i ω *
          ((Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) ^ 2 -
            (h n i : ℝ) * X.σ ^ 2)))
    (hL1 : Tendsto (fun n => ∫⁻ ω, ‖F n ω - f ω‖ₑ ∂P)
      atTop (nhds 0)) :
    (∫ ω, f ω ∂P) = 0 := by sorry
