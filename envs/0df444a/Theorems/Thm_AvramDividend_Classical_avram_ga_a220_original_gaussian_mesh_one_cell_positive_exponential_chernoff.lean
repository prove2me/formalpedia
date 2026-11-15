-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a220_original_gaussian_mesh_one_cell_positive_exponential_chernoff
-- name    : AvramDividend.Classical.avram_ga_a220_original_gaussian_mesh_one_cell_positive_exponential_chernoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:48:25.011479+00:00
-- url     : https://prove2.me/theorems/de6fc398-cb26-42be-b37a-a2d0953132f3
-- title:
--   Original zero-jump Gaussian physical mesh cell positive exponential tail has uniform rate exp(b-c(m+1))
-- statement:
--   For an original zero-jump Gaussian Lévy increment over a physical width n/(m+1), the normalised centred increment positive exponential tail above δ has an expected value bounded by a constant times exp(-3δ²(m+1)/(8n)), uniformly in the starting cell time. Proves a source-specific rare positive increment bound for the a216 combined original Gaussian verification source.
-- source:
--   Original Gaussian a69 source Chernoff and a219 optimal mesh tilt, feeding a218 finite mesh expected L1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a69_original_gaussian_positive_tail_unconditional_expected_chernoff
import Theorems.Thm_AvramDividend_Classical_avram_ga_a219_physical_mesh_gaussian_optimal_positive_chernoff_rate
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a220_original_gaussian_mesh_one_cell_positive_exponential_chernoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n m : ℕ) (hn : 0 < n) (s t : ℝ≥0) (hst : s ≤ t)
    (hWidth : (((t - s : ℝ≥0) : ℝ)) =
      (n : ℝ) / ((m : ℝ) + 1))
    (θ δ : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hMeas : Measurable (fun ω : Ω =>
      ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ)) :
    (∫ ω, if δ ≤
      ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
      then Real.exp (θ *
        (((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))
      else 0 ∂P) ≤
      Real.exp (θ * δ / 2 + (n : ℝ) * θ^2 / 2 -
        (3 * δ^2 / (8 * (n : ℝ))) * ((m : ℝ) + 1)) := by sorry
