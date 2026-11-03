-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_full_future_source_law
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_full_future_source_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:24:11.844321+00:00
-- url     : https://prove2.me/theorems/d2b96f8c-68b2-4212-b39b-e66894f16fbc
-- title:
--   Original right-continuous stopping time preserves full future Lévy source path law
-- statement:
--   For any genuinely finite stopping time of the right-continuous filtration of the original spectrally negative Lévy source, the entire actual random post-stop path t↦X.X(τ+t)−X.Xτ, on the original Ω and original P, has exactly the same probability law on the path product measurable space as the original path t↦X.Xt. This is valid for arbitrary source ν and σ, including σ=0. Apply the Proved same-path right-continuous source lift and Proved strong Markov whole-path stationarity at finite stopping times. This is an original-process localisation input for the controlled Itô formula, not a construction of the continuous Gaussian residual or a Brownian copy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_full_future_source_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s}) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
  sorry
