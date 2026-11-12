-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB83_original_two_mesh_common_refinement_bilinear
-- name    : AvramDividend.Classical.avram_gbB83_original_two_mesh_common_refinement_bilinear
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T17:38:55.456652+00:00
-- url     : https://prove2.me/theorems/ae17e63a-fb7a-4e33-8e0d-44451d6c43f0
-- title:
--   Original Gaussian two-mesh mixed covariance on exact uniform common refinement
-- statement:
--   The covariance of two original-process Gaussian compensated predictable uniform-grid sums equals sigma squared times the common-refinement fine cell width times the finite sum of expected products of the coarse coefficient values at each fine cell. Prove by common-refinement deterministic block regrouping, actual filtration predictability, and the proved one-grid bilinear covariance B77.
-- source:
--   Direct child for original two-grid generic covariance B76, combined with deterministic step overlap B78.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB83_original_two_mesh_common_refinement_bilinear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ)
    (hAdapt : ∀ (m i : ℕ),
      Measurable[𝓕.rightCont
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))]
        (G m i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ m i ω, |G m i ω| ≤ B) :
    let L : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        G m i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
          (Δ : ℝ) * X.c))
    ∀ m l,
      (∫ ω, L m ω * L l ω ∂P) =
        (X.σ ^ 2) * ((n : ℝ) / (((m + 1) * (l + 1) : ℕ) : ℝ)) *
          (Finset.range ((m + 1) * (l + 1))).sum (fun r =>
            ∫ ω, G m (r / (l + 1)) ω *
              G l (r / (m + 1)) ω ∂P) := by sorry
